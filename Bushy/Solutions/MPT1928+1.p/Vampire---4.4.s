%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_6__t26_yellow_6.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:54 EDT 2019

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       : 1234 (6072 expanded)
%              Number of leaves         :  314 (2453 expanded)
%              Depth                    :   21
%              Number of atoms          : 3482 (19112 expanded)
%              Number of equality atoms :   23 ( 170 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f145,f152,f159,f166,f173,f180,f187,f194,f201,f209,f219,f226,f234,f242,f253,f261,f269,f277,f285,f293,f300,f309,f317,f325,f334,f342,f351,f359,f367,f380,f387,f394,f401,f408,f417,f425,f433,f442,f450,f458,f467,f484,f492,f499,f515,f522,f529,f537,f550,f558,f566,f574,f583,f603,f611,f619,f639,f647,f664,f675,f683,f691,f698,f705,f712,f719,f726,f733,f740,f749,f756,f781,f800,f807,f829,f840,f848,f859,f870,f878,f886,f897,f904,f912,f920,f956,f964,f974,f989,f996,f1003,f1010,f1017,f1024,f1031,f1038,f1047,f1215,f1224,f1231,f1239,f1248,f1255,f1263,f1272,f1280,f1321,f1340,f1347,f1358,f1366,f1430,f1441,f1449,f1519,f1530,f1606,f1614,f1625,f1707,f1722,f1760,f1789,f1796,f1822,f1829,f1846,f1853,f1890,f1948,f1962,f1993,f2004,f2012,f2031,f2038,f2057,f2113,f2137,f2144,f2178,f2201,f2202,f2236,f2290,f2298,f2305,f2307,f2309,f2311,f2318,f2356,f2386,f2393,f2451,f2458,f2500,f2529,f2536,f2543,f2545,f2595,f2698,f2705,f2712,f2751,f2777,f2808,f2815,f2822,f2839,f2846,f2880,f2882,f2884,f2886,f2901,f2928,f2930,f2932,f2967,f2974,f2997,f3028,f3145,f3205,f3239,f3252,f3261,f3272,f3283,f3290,f3297,f3318,f3325,f3353,f3360,f3384,f3405,f3412,f3426,f3466,f3473,f3484,f3494,f3508,f3510,f3512,f3514,f3516,f3518,f3520,f3522,f3524,f3593,f3624,f3640,f3645,f3652,f3659,f3684,f3733,f3734,f3735,f3736,f3737,f3738,f3739,f3740,f3744,f3747,f3750,f3752,f3754,f3756,f3758,f3760,f3762,f3790,f3803,f3850,f3876,f3889,f3927,f3958,f4006,f4017,f4024,f4031,f4069,f4076,f4083,f4090,f4097,f4220,f4227,f4234,f4249,f4256,f4264,f4272,f4279,f4294,f4301,f4308,f4319,f4326,f4333,f4408,f4415,f4422,f4429,f4436,f4443,f4450,f4457,f4464,f4471,f4478,f4485,f4500,f4538,f4572,f4579,f4586,f4595,f4602,f4610,f4618,f4625,f4632,f4639,f4657,f4665,f4674,f4681,f4702,f4737,f4744,f4802,f4809,f4816,f4854,f4895,f4897])).

fof(f4897,plain,
    ( ~ spl14_26
    | ~ spl14_470
    | ~ spl14_486 ),
    inference(avatar_contradiction_clause,[],[f4896])).

fof(f4896,plain,
    ( $false
    | ~ spl14_26
    | ~ spl14_470
    | ~ spl14_486 ),
    inference(subsumption_resolution,[],[f4855,f4585])).

fof(f4585,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_486 ),
    inference(avatar_component_clause,[],[f4584])).

fof(f4584,plain,
    ( spl14_486
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_486])])).

fof(f4855,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_26
    | ~ spl14_470 ),
    inference(unit_resulting_resolution,[],[f233,f4463,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK11(X0,X1),X1)
          & r2_hidden(sK11(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f45,f83])).

fof(f83,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK11(X0,X1),X1)
        & r2_hidden(sK11(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t3_xboole_0)).

fof(f4463,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK3)
    | ~ spl14_470 ),
    inference(avatar_component_clause,[],[f4462])).

fof(f4462,plain,
    ( spl14_470
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_470])])).

fof(f233,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl14_26 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl14_26
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_26])])).

fof(f4895,plain,
    ( ~ spl14_14
    | ~ spl14_470
    | ~ spl14_486 ),
    inference(avatar_contradiction_clause,[],[f4894])).

fof(f4894,plain,
    ( $false
    | ~ spl14_14
    | ~ spl14_470
    | ~ spl14_486 ),
    inference(subsumption_resolution,[],[f4859,f4585])).

fof(f4859,plain,
    ( ~ r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_14
    | ~ spl14_470 ),
    inference(unit_resulting_resolution,[],[f186,f4463,f115])).

fof(f186,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl14_14
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f4854,plain,
    ( ~ spl14_525
    | ~ spl14_278
    | ~ spl14_518 ),
    inference(avatar_split_clause,[],[f4834,f4800,f2111,f4852])).

fof(f4852,plain,
    ( spl14_525
  <=> ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_525])])).

fof(f2111,plain,
    ( spl14_278
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_278])])).

fof(f4800,plain,
    ( spl14_518
  <=> r2_hidden(sK10(sK10(sK2)),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_518])])).

fof(f4834,plain,
    ( ~ m1_subset_1(sK10(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_518 ),
    inference(unit_resulting_resolution,[],[f4801,f3604])).

fof(f3604,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl14_278 ),
    inference(resolution,[],[f2112,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t5_subset)).

fof(f2112,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_278 ),
    inference(avatar_component_clause,[],[f2111])).

fof(f4801,plain,
    ( r2_hidden(sK10(sK10(sK2)),sK10(sK2))
    | ~ spl14_518 ),
    inference(avatar_component_clause,[],[f4800])).

fof(f4816,plain,
    ( ~ spl14_523
    | spl14_513 ),
    inference(avatar_split_clause,[],[f4727,f4700,f4814])).

fof(f4814,plain,
    ( spl14_523
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK10(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_523])])).

fof(f4700,plain,
    ( spl14_513
  <=> ~ m1_subset_1(sK2,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_513])])).

fof(f4727,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(sK10(sK2))))
    | ~ spl14_513 ),
    inference(unit_resulting_resolution,[],[f112,f4701,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t4_subset)).

fof(f4701,plain,
    ( ~ m1_subset_1(sK2,sK10(sK2))
    | ~ spl14_513 ),
    inference(avatar_component_clause,[],[f4700])).

fof(f112,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f21,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',existence_m1_subset_1)).

fof(f4809,plain,
    ( ~ spl14_521
    | spl14_511 ),
    inference(avatar_split_clause,[],[f4707,f4691,f4807])).

fof(f4807,plain,
    ( spl14_521
  <=> ~ r2_hidden(sK10(sK2),sK10(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_521])])).

fof(f4691,plain,
    ( spl14_511
  <=> ~ v1_xboole_0(sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_511])])).

fof(f4707,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(sK10(sK2)))
    | ~ spl14_511 ),
    inference(unit_resulting_resolution,[],[f112,f4692,f326])).

fof(f326,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f119,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',antisymmetry_r2_hidden)).

fof(f119,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t2_subset)).

fof(f4692,plain,
    ( ~ v1_xboole_0(sK10(sK2))
    | ~ spl14_511 ),
    inference(avatar_component_clause,[],[f4691])).

fof(f4802,plain,
    ( spl14_518
    | spl14_511 ),
    inference(avatar_split_clause,[],[f4703,f4691,f4800])).

fof(f4703,plain,
    ( r2_hidden(sK10(sK10(sK2)),sK10(sK2))
    | ~ spl14_511 ),
    inference(unit_resulting_resolution,[],[f112,f4692,f119])).

fof(f4744,plain,
    ( ~ spl14_517
    | spl14_511 ),
    inference(avatar_split_clause,[],[f4717,f4691,f4742])).

fof(f4742,plain,
    ( spl14_517
  <=> ~ r1_xboole_0(sK10(sK2),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_517])])).

fof(f4717,plain,
    ( ~ r1_xboole_0(sK10(sK2),sK10(sK2))
    | ~ spl14_511 ),
    inference(unit_resulting_resolution,[],[f112,f4692,f1715])).

fof(f1715,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f1714])).

fof(f1714,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r1_xboole_0(X0,X0)
      | ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(factoring,[],[f792])).

fof(f792,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ m1_subset_1(X2,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,X0) ) ),
    inference(resolution,[],[f344,f119])).

fof(f344,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X2,X1) ) ),
    inference(resolution,[],[f115,f119])).

fof(f4737,plain,
    ( ~ spl14_515
    | spl14_511 ),
    inference(avatar_split_clause,[],[f4712,f4691,f4735])).

fof(f4735,plain,
    ( spl14_515
  <=> ~ m1_subset_1(sK10(sK2),sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_515])])).

fof(f4712,plain,
    ( ~ m1_subset_1(sK10(sK2),sK10(sK2))
    | ~ spl14_511 ),
    inference(unit_resulting_resolution,[],[f4692,f762])).

fof(f762,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f761])).

fof(f761,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,X0)
      | ~ m1_subset_1(X0,X0) ) ),
    inference(factoring,[],[f530])).

fof(f530,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f326,f119])).

fof(f4702,plain,
    ( spl14_510
    | ~ spl14_513
    | ~ spl14_410 ),
    inference(avatar_split_clause,[],[f4142,f4015,f4700,f4694])).

fof(f4694,plain,
    ( spl14_510
  <=> v1_xboole_0(sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_510])])).

fof(f4015,plain,
    ( spl14_410
  <=> r2_hidden(sK10(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_410])])).

fof(f4142,plain,
    ( ~ m1_subset_1(sK2,sK10(sK2))
    | v1_xboole_0(sK10(sK2))
    | ~ spl14_410 ),
    inference(resolution,[],[f4016,f326])).

fof(f4016,plain,
    ( r2_hidden(sK10(sK2),sK2)
    | ~ spl14_410 ),
    inference(avatar_component_clause,[],[f4015])).

fof(f4681,plain,
    ( ~ spl14_509
    | spl14_441 ),
    inference(avatar_split_clause,[],[f4284,f4277,f4679])).

fof(f4679,plain,
    ( spl14_509
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_509])])).

fof(f4277,plain,
    ( spl14_441
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_441])])).

fof(f4284,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_441 ),
    inference(unit_resulting_resolution,[],[f112,f4278,f126])).

fof(f4278,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_441 ),
    inference(avatar_component_clause,[],[f4277])).

fof(f4674,plain,
    ( ~ spl14_507
    | spl14_439 ),
    inference(avatar_split_clause,[],[f4280,f4270,f4672])).

fof(f4672,plain,
    ( spl14_507
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_507])])).

fof(f4270,plain,
    ( spl14_439
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_439])])).

fof(f4280,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_439 ),
    inference(unit_resulting_resolution,[],[f112,f4271,f126])).

fof(f4271,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_439 ),
    inference(avatar_component_clause,[],[f4270])).

fof(f4665,plain,
    ( ~ spl14_505
    | spl14_501 ),
    inference(avatar_split_clause,[],[f4648,f4637,f4663])).

fof(f4663,plain,
    ( spl14_505
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK11(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_505])])).

fof(f4637,plain,
    ( spl14_501
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK11(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_501])])).

fof(f4648,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK11(sK3,sK3)))
    | ~ spl14_501 ),
    inference(unit_resulting_resolution,[],[f4638,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t1_subset)).

fof(f4638,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK11(sK3,sK3)))
    | ~ spl14_501 ),
    inference(avatar_component_clause,[],[f4637])).

fof(f4657,plain,
    ( ~ spl14_503
    | spl14_499 ),
    inference(avatar_split_clause,[],[f4644,f4630,f4655])).

fof(f4655,plain,
    ( spl14_503
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK11(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_503])])).

fof(f4630,plain,
    ( spl14_499
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK11(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_499])])).

fof(f4644,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK11(sK2,sK2)))
    | ~ spl14_499 ),
    inference(unit_resulting_resolution,[],[f4631,f118])).

fof(f4631,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK11(sK2,sK2)))
    | ~ spl14_499 ),
    inference(avatar_component_clause,[],[f4630])).

fof(f4639,plain,
    ( ~ spl14_501
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f4380,f4331,f4637])).

fof(f4331,plain,
    ( spl14_452
  <=> r2_hidden(sK11(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_452])])).

fof(f4380,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK11(sK3,sK3)))
    | ~ spl14_452 ),
    inference(unit_resulting_resolution,[],[f4332,f765])).

fof(f765,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f763,f127])).

fof(f763,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f762,f126])).

fof(f4332,plain,
    ( r2_hidden(sK11(sK3,sK3),sK3)
    | ~ spl14_452 ),
    inference(avatar_component_clause,[],[f4331])).

fof(f4632,plain,
    ( ~ spl14_499
    | ~ spl14_448 ),
    inference(avatar_split_clause,[],[f4346,f4317,f4630])).

fof(f4317,plain,
    ( spl14_448
  <=> r2_hidden(sK11(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_448])])).

fof(f4346,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK11(sK2,sK2)))
    | ~ spl14_448 ),
    inference(unit_resulting_resolution,[],[f4318,f765])).

fof(f4318,plain,
    ( r2_hidden(sK11(sK2,sK2),sK2)
    | ~ spl14_448 ),
    inference(avatar_component_clause,[],[f4317])).

fof(f4625,plain,
    ( ~ spl14_497
    | spl14_429 ),
    inference(avatar_split_clause,[],[f4239,f4225,f4623])).

fof(f4623,plain,
    ( spl14_497
  <=> ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_497])])).

fof(f4225,plain,
    ( spl14_429
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_429])])).

fof(f4239,plain,
    ( ~ r2_hidden(sK3,sK10(k1_zfmisc_1(k1_zfmisc_1(sK2))))
    | ~ spl14_429 ),
    inference(unit_resulting_resolution,[],[f112,f4226,f126])).

fof(f4226,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl14_429 ),
    inference(avatar_component_clause,[],[f4225])).

fof(f4618,plain,
    ( ~ spl14_495
    | spl14_427 ),
    inference(avatar_split_clause,[],[f4235,f4218,f4616])).

fof(f4616,plain,
    ( spl14_495
  <=> ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_495])])).

fof(f4218,plain,
    ( spl14_427
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_427])])).

fof(f4235,plain,
    ( ~ r2_hidden(sK2,sK10(k1_zfmisc_1(k1_zfmisc_1(sK3))))
    | ~ spl14_427 ),
    inference(unit_resulting_resolution,[],[f112,f4219,f126])).

fof(f4219,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl14_427 ),
    inference(avatar_component_clause,[],[f4218])).

fof(f4610,plain,
    ( spl14_492
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_212
    | ~ spl14_342 ),
    inference(avatar_split_clause,[],[f3327,f3026,f1278,f199,f178,f150,f143,f136,f4608])).

fof(f4608,plain,
    ( spl14_492
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_492])])).

fof(f136,plain,
    ( spl14_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f143,plain,
    ( spl14_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f150,plain,
    ( spl14_5
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f178,plain,
    ( spl14_12
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f199,plain,
    ( spl14_18
  <=> r1_waybel_0(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_18])])).

fof(f1278,plain,
    ( spl14_212
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_212])])).

fof(f3026,plain,
    ( spl14_342
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_342])])).

fof(f3327,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))),sK3)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_212
    | ~ spl14_342 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f1279,f3027,f108])).

fof(f108,plain,(
    ! [X6,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | r2_hidden(k2_waybel_0(X0,X1,X6),X2)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
                      & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
                      & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ( ! [X6] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                      | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
                      | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f77,f79,f78])).

fof(f78,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
          & r1_orders_2(X1,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_hidden(k2_waybel_0(X0,X1,sK8(X0,X1,X2,X3)),X2)
        & r1_orders_2(X1,X3,sK8(X0,X1,X2,X3))
        & m1_subset_1(sK8(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
              | ~ r1_orders_2(X1,X5,X6)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
            | ~ r1_orders_2(X1,sK9(X0,X1,X2),X6)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X5] :
                    ( ! [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        | ~ r1_orders_2(X1,X5,X6)
                        | ~ m1_subset_1(X6,u1_struct_0(X1)) )
                    & m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_waybel_0(X0,X1,X2)
                | ! [X3] :
                    ( ? [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ? [X3] :
                    ( ! [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r1_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,X3,X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r1_waybel_0(X0,X1,X2)
            <=> ? [X3] :
                  ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ( r1_orders_2(X1,X3,X4)
                       => r2_hidden(k2_waybel_0(X0,X1,X4),X2) ) )
                  & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',d11_waybel_0)).

fof(f3027,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)))
    | ~ spl14_342 ),
    inference(avatar_component_clause,[],[f3026])).

fof(f1279,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_212 ),
    inference(avatar_component_clause,[],[f1278])).

fof(f200,plain,
    ( r1_waybel_0(sK0,sK1,sK3)
    | ~ spl14_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f179,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f178])).

fof(f151,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl14_5 ),
    inference(avatar_component_clause,[],[f150])).

fof(f144,plain,
    ( l1_struct_0(sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f143])).

fof(f137,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f136])).

fof(f4602,plain,
    ( ~ spl14_491
    | spl14_425 ),
    inference(avatar_split_clause,[],[f4210,f4095,f4600])).

fof(f4600,plain,
    ( spl14_491
  <=> ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_491])])).

fof(f4095,plain,
    ( spl14_425
  <=> ~ m1_subset_1(sK10(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_425])])).

fof(f4210,plain,
    ( ~ r2_hidden(sK10(sK3),sK10(k1_zfmisc_1(sK2)))
    | ~ spl14_425 ),
    inference(unit_resulting_resolution,[],[f112,f4096,f126])).

fof(f4096,plain,
    ( ~ m1_subset_1(sK10(sK3),sK2)
    | ~ spl14_425 ),
    inference(avatar_component_clause,[],[f4095])).

fof(f4595,plain,
    ( ~ spl14_489
    | spl14_423 ),
    inference(avatar_split_clause,[],[f4205,f4088,f4593])).

fof(f4593,plain,
    ( spl14_489
  <=> ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_489])])).

fof(f4088,plain,
    ( spl14_423
  <=> ~ m1_subset_1(sK10(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_423])])).

fof(f4205,plain,
    ( ~ r2_hidden(sK10(sK2),sK10(k1_zfmisc_1(sK3)))
    | ~ spl14_423 ),
    inference(unit_resulting_resolution,[],[f112,f4089,f126])).

fof(f4089,plain,
    ( ~ m1_subset_1(sK10(sK2),sK3)
    | ~ spl14_423 ),
    inference(avatar_component_clause,[],[f4088])).

fof(f4586,plain,
    ( spl14_486
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_206
    | ~ spl14_338 ),
    inference(avatar_split_clause,[],[f3299,f2972,f1253,f192,f178,f150,f143,f136,f4584])).

fof(f192,plain,
    ( spl14_16
  <=> r1_waybel_0(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_16])])).

fof(f1253,plain,
    ( spl14_206
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_206])])).

fof(f2972,plain,
    ( spl14_338
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_338])])).

fof(f3299,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_206
    | ~ spl14_338 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f1254,f2973,f108])).

fof(f2973,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)))
    | ~ spl14_338 ),
    inference(avatar_component_clause,[],[f2972])).

fof(f1254,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_206 ),
    inference(avatar_component_clause,[],[f1253])).

fof(f193,plain,
    ( r1_waybel_0(sK0,sK1,sK2)
    | ~ spl14_16 ),
    inference(avatar_component_clause,[],[f192])).

fof(f4579,plain,
    ( ~ spl14_485
    | spl14_457 ),
    inference(avatar_split_clause,[],[f4491,f4413,f4577])).

fof(f4577,plain,
    ( spl14_485
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_485])])).

fof(f4413,plain,
    ( spl14_457
  <=> ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_457])])).

fof(f4491,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK10(sK3)))
    | ~ spl14_457 ),
    inference(unit_resulting_resolution,[],[f4414,f118])).

fof(f4414,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK3)))
    | ~ spl14_457 ),
    inference(avatar_component_clause,[],[f4413])).

fof(f4572,plain,
    ( ~ spl14_483
    | spl14_455 ),
    inference(avatar_split_clause,[],[f4487,f4406,f4570])).

fof(f4570,plain,
    ( spl14_483
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_483])])).

fof(f4406,plain,
    ( spl14_455
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_455])])).

fof(f4487,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK10(sK2)))
    | ~ spl14_455 ),
    inference(unit_resulting_resolution,[],[f4407,f118])).

fof(f4407,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK2)))
    | ~ spl14_455 ),
    inference(avatar_component_clause,[],[f4406])).

fof(f4538,plain,
    ( spl14_480
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_214
    | ~ spl14_336 ),
    inference(avatar_split_clause,[],[f3265,f2844,f1319,f199,f178,f150,f143,f136,f4536])).

fof(f4536,plain,
    ( spl14_480
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_480])])).

fof(f1319,plain,
    ( spl14_214
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_214])])).

fof(f2844,plain,
    ( spl14_336
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_336])])).

fof(f3265,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3))),sK3)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_214
    | ~ spl14_336 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f1320,f2845,f108])).

fof(f2845,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3)))
    | ~ spl14_336 ),
    inference(avatar_component_clause,[],[f2844])).

fof(f1320,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_214 ),
    inference(avatar_component_clause,[],[f1319])).

fof(f4500,plain,
    ( spl14_478
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_212
    | ~ spl14_328 ),
    inference(avatar_split_clause,[],[f3245,f2806,f1278,f192,f178,f150,f143,f136,f4498])).

fof(f4498,plain,
    ( spl14_478
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_478])])).

fof(f2806,plain,
    ( spl14_328
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_328])])).

fof(f3245,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_212
    | ~ spl14_328 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f1279,f2807,f108])).

fof(f2807,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)))
    | ~ spl14_328 ),
    inference(avatar_component_clause,[],[f2806])).

fof(f4485,plain,
    ( ~ spl14_477
    | ~ spl14_26
    | spl14_399
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f4379,f4331,f3848,f232,f4483])).

fof(f4483,plain,
    ( spl14_477
  <=> ~ m1_subset_1(sK11(sK3,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_477])])).

fof(f3848,plain,
    ( spl14_399
  <=> ~ v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_399])])).

fof(f4379,plain,
    ( ~ m1_subset_1(sK11(sK3,sK3),sK2)
    | ~ spl14_26
    | ~ spl14_399
    | ~ spl14_452 ),
    inference(unit_resulting_resolution,[],[f3849,f233,f4332,f344])).

fof(f3849,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl14_399 ),
    inference(avatar_component_clause,[],[f3848])).

fof(f4478,plain,
    ( spl14_474
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f4376,f4331,f4476])).

fof(f4476,plain,
    ( spl14_474
  <=> m1_subset_1(sK11(sK3,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_474])])).

fof(f4376,plain,
    ( m1_subset_1(sK11(sK3,sK3),sK3)
    | ~ spl14_452 ),
    inference(unit_resulting_resolution,[],[f4332,f118])).

fof(f4471,plain,
    ( ~ spl14_473
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f4375,f4331,f4469])).

fof(f4469,plain,
    ( spl14_473
  <=> ~ r2_hidden(sK3,sK11(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_473])])).

fof(f4375,plain,
    ( ~ r2_hidden(sK3,sK11(sK3,sK3))
    | ~ spl14_452 ),
    inference(unit_resulting_resolution,[],[f4332,f117])).

fof(f4464,plain,
    ( spl14_470
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_206
    | ~ spl14_322 ),
    inference(avatar_split_clause,[],[f3194,f2749,f1253,f199,f178,f150,f143,f136,f4462])).

fof(f2749,plain,
    ( spl14_322
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_322])])).

fof(f3194,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2))),sK3)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_206
    | ~ spl14_322 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f1254,f2750,f108])).

fof(f2750,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)))
    | ~ spl14_322 ),
    inference(avatar_component_clause,[],[f2749])).

fof(f4457,plain,
    ( ~ spl14_469
    | ~ spl14_14
    | ~ spl14_452 ),
    inference(avatar_split_clause,[],[f4372,f4331,f185,f4455])).

fof(f4455,plain,
    ( spl14_469
  <=> ~ r2_hidden(sK11(sK3,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_469])])).

fof(f4372,plain,
    ( ~ r2_hidden(sK11(sK3,sK3),sK2)
    | ~ spl14_14
    | ~ spl14_452 ),
    inference(unit_resulting_resolution,[],[f186,f4332,f115])).

fof(f4450,plain,
    ( ~ spl14_467
    | ~ spl14_14
    | spl14_405
    | ~ spl14_448 ),
    inference(avatar_split_clause,[],[f4345,f4317,f3925,f185,f4448])).

fof(f4448,plain,
    ( spl14_467
  <=> ~ m1_subset_1(sK11(sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_467])])).

fof(f3925,plain,
    ( spl14_405
  <=> ~ v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_405])])).

fof(f4345,plain,
    ( ~ m1_subset_1(sK11(sK2,sK2),sK3)
    | ~ spl14_14
    | ~ spl14_405
    | ~ spl14_448 ),
    inference(unit_resulting_resolution,[],[f3926,f186,f4318,f344])).

fof(f3926,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl14_405 ),
    inference(avatar_component_clause,[],[f3925])).

fof(f4443,plain,
    ( spl14_464
    | ~ spl14_448 ),
    inference(avatar_split_clause,[],[f4342,f4317,f4441])).

fof(f4441,plain,
    ( spl14_464
  <=> m1_subset_1(sK11(sK2,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_464])])).

fof(f4342,plain,
    ( m1_subset_1(sK11(sK2,sK2),sK2)
    | ~ spl14_448 ),
    inference(unit_resulting_resolution,[],[f4318,f118])).

fof(f4436,plain,
    ( ~ spl14_463
    | ~ spl14_448 ),
    inference(avatar_split_clause,[],[f4341,f4317,f4434])).

fof(f4434,plain,
    ( spl14_463
  <=> ~ r2_hidden(sK2,sK11(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_463])])).

fof(f4341,plain,
    ( ~ r2_hidden(sK2,sK11(sK2,sK2))
    | ~ spl14_448 ),
    inference(unit_resulting_resolution,[],[f4318,f117])).

fof(f4429,plain,
    ( ~ spl14_461
    | ~ spl14_26
    | ~ spl14_448 ),
    inference(avatar_split_clause,[],[f4338,f4317,f232,f4427])).

fof(f4427,plain,
    ( spl14_461
  <=> ~ r2_hidden(sK11(sK2,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_461])])).

fof(f4338,plain,
    ( ~ r2_hidden(sK11(sK2,sK2),sK3)
    | ~ spl14_26
    | ~ spl14_448 ),
    inference(unit_resulting_resolution,[],[f233,f4318,f115])).

fof(f4422,plain,
    ( spl14_458
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_198
    | ~ spl14_318 ),
    inference(avatar_split_clause,[],[f3138,f2703,f1222,f192,f178,f150,f143,f136,f4420])).

fof(f4420,plain,
    ( spl14_458
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_458])])).

fof(f1222,plain,
    ( spl14_198
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_198])])).

fof(f2703,plain,
    ( spl14_318
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_318])])).

fof(f3138,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_198
    | ~ spl14_318 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f1223,f2704,f108])).

fof(f2704,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2)))
    | ~ spl14_318 ),
    inference(avatar_component_clause,[],[f2703])).

fof(f1223,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_198 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f4415,plain,
    ( ~ spl14_457
    | ~ spl14_384 ),
    inference(avatar_split_clause,[],[f3903,f3492,f4413])).

fof(f3492,plain,
    ( spl14_384
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_384])])).

fof(f3903,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK10(sK3)))
    | ~ spl14_384 ),
    inference(unit_resulting_resolution,[],[f112,f3493,f785])).

fof(f785,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,X7)
      | ~ m1_subset_1(X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f770,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t7_boole)).

fof(f770,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f765,f119])).

fof(f3493,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl14_384 ),
    inference(avatar_component_clause,[],[f3492])).

fof(f4408,plain,
    ( ~ spl14_455
    | ~ spl14_378 ),
    inference(avatar_split_clause,[],[f3826,f3464,f4406])).

fof(f3464,plain,
    ( spl14_378
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_378])])).

fof(f3826,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK10(sK2)))
    | ~ spl14_378 ),
    inference(unit_resulting_resolution,[],[f112,f3465,f785])).

fof(f3465,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl14_378 ),
    inference(avatar_component_clause,[],[f3464])).

fof(f4333,plain,
    ( spl14_452
    | ~ spl14_384 ),
    inference(avatar_split_clause,[],[f3906,f3492,f4331])).

fof(f3906,plain,
    ( r2_hidden(sK11(sK3,sK3),sK3)
    | ~ spl14_384 ),
    inference(unit_resulting_resolution,[],[f112,f3493,f1729])).

fof(f1729,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(X13,X12)
      | r2_hidden(sK11(X12,X12),X12)
      | ~ m1_subset_1(X11,X12) ) ),
    inference(resolution,[],[f1723,f124])).

fof(f1723,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | r2_hidden(sK11(X0,X0),X0) ) ),
    inference(resolution,[],[f1715,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK11(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f4326,plain,
    ( spl14_450
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_192 ),
    inference(avatar_split_clause,[],[f1208,f1036,f178,f150,f143,f136,f4324])).

fof(f4324,plain,
    ( spl14_450
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_450])])).

fof(f1036,plain,
    ( spl14_192
  <=> m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_192])])).

fof(f1208,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_192 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f1037,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_waybel_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',dt_k2_waybel_0)).

fof(f1037,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_192 ),
    inference(avatar_component_clause,[],[f1036])).

fof(f4319,plain,
    ( spl14_448
    | ~ spl14_378 ),
    inference(avatar_split_clause,[],[f3829,f3464,f4317])).

fof(f3829,plain,
    ( r2_hidden(sK11(sK2,sK2),sK2)
    | ~ spl14_378 ),
    inference(unit_resulting_resolution,[],[f112,f3465,f1729])).

fof(f4308,plain,
    ( ~ spl14_447
    | spl14_441 ),
    inference(avatar_split_clause,[],[f4285,f4277,f4306])).

fof(f4306,plain,
    ( spl14_447
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_447])])).

fof(f4285,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_441 ),
    inference(unit_resulting_resolution,[],[f4278,f118])).

fof(f4301,plain,
    ( ~ spl14_445
    | spl14_439 ),
    inference(avatar_split_clause,[],[f4281,f4270,f4299])).

fof(f4299,plain,
    ( spl14_445
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_445])])).

fof(f4281,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_439 ),
    inference(unit_resulting_resolution,[],[f4271,f118])).

fof(f4294,plain,
    ( spl14_442
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_190 ),
    inference(avatar_split_clause,[],[f1159,f1029,f178,f150,f143,f136,f4292])).

fof(f4292,plain,
    ( spl14_442
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_442])])).

fof(f1029,plain,
    ( spl14_190
  <=> m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_190])])).

fof(f1159,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_190 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f1030,f125])).

fof(f1030,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_190 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f4279,plain,
    ( ~ spl14_441
    | ~ spl14_278
    | ~ spl14_384 ),
    inference(avatar_split_clause,[],[f3907,f3492,f2111,f4277])).

fof(f3907,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_384 ),
    inference(unit_resulting_resolution,[],[f3493,f3604])).

fof(f4272,plain,
    ( ~ spl14_439
    | ~ spl14_278
    | ~ spl14_378 ),
    inference(avatar_split_clause,[],[f3830,f3464,f2111,f4270])).

fof(f3830,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_378 ),
    inference(unit_resulting_resolution,[],[f3465,f3604])).

fof(f4264,plain,
    ( spl14_436
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_188 ),
    inference(avatar_split_clause,[],[f1116,f1022,f178,f150,f143,f136,f4262])).

fof(f4262,plain,
    ( spl14_436
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_436])])).

fof(f1022,plain,
    ( spl14_188
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_188])])).

fof(f1116,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_188 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f1023,f125])).

fof(f1023,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_188 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f4256,plain,
    ( ~ spl14_435
    | spl14_429 ),
    inference(avatar_split_clause,[],[f4240,f4225,f4254])).

fof(f4254,plain,
    ( spl14_435
  <=> ~ r2_hidden(sK3,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_435])])).

fof(f4240,plain,
    ( ~ r2_hidden(sK3,k1_zfmisc_1(sK2))
    | ~ spl14_429 ),
    inference(unit_resulting_resolution,[],[f4226,f118])).

fof(f4249,plain,
    ( ~ spl14_433
    | spl14_427 ),
    inference(avatar_split_clause,[],[f4236,f4218,f4247])).

fof(f4247,plain,
    ( spl14_433
  <=> ~ r2_hidden(sK2,k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_433])])).

fof(f4236,plain,
    ( ~ r2_hidden(sK2,k1_zfmisc_1(sK3))
    | ~ spl14_427 ),
    inference(unit_resulting_resolution,[],[f4219,f118])).

fof(f4234,plain,
    ( spl14_430
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_182 ),
    inference(avatar_split_clause,[],[f1079,f1001,f178,f150,f143,f136,f4232])).

fof(f4232,plain,
    ( spl14_430
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_430])])).

fof(f1001,plain,
    ( spl14_182
  <=> m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_182])])).

fof(f1079,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_182 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f1002,f125])).

fof(f1002,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_182 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f4227,plain,
    ( ~ spl14_429
    | ~ spl14_416
    | spl14_425 ),
    inference(avatar_split_clause,[],[f4209,f4095,f4067,f4225])).

fof(f4067,plain,
    ( spl14_416
  <=> r2_hidden(sK10(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_416])])).

fof(f4209,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK2))
    | ~ spl14_416
    | ~ spl14_425 ),
    inference(unit_resulting_resolution,[],[f4068,f4096,f126])).

fof(f4068,plain,
    ( r2_hidden(sK10(sK3),sK3)
    | ~ spl14_416 ),
    inference(avatar_component_clause,[],[f4067])).

fof(f4220,plain,
    ( ~ spl14_427
    | ~ spl14_410
    | spl14_423 ),
    inference(avatar_split_clause,[],[f4204,f4088,f4015,f4218])).

fof(f4204,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK3))
    | ~ spl14_410
    | ~ spl14_423 ),
    inference(unit_resulting_resolution,[],[f4016,f4089,f126])).

fof(f4097,plain,
    ( ~ spl14_425
    | ~ spl14_14
    | spl14_399
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3942,f3925,f3848,f185,f4095])).

fof(f3942,plain,
    ( ~ m1_subset_1(sK10(sK3),sK2)
    | ~ spl14_14
    | ~ spl14_399
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f3849,f112,f186,f3926,f792])).

fof(f4090,plain,
    ( ~ spl14_423
    | ~ spl14_14
    | spl14_399
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3941,f3925,f3848,f185,f4088])).

fof(f3941,plain,
    ( ~ m1_subset_1(sK10(sK2),sK3)
    | ~ spl14_14
    | ~ spl14_399
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f112,f3849,f186,f3926,f792])).

fof(f4083,plain,
    ( ~ spl14_421
    | ~ spl14_14
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3932,f3925,f185,f4081])).

fof(f4081,plain,
    ( spl14_421
  <=> ~ r2_hidden(sK10(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_421])])).

fof(f3932,plain,
    ( ~ r2_hidden(sK10(sK3),sK2)
    | ~ spl14_14
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f112,f186,f3926,f344])).

fof(f4076,plain,
    ( ~ spl14_419
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3930,f3925,f4074])).

fof(f4074,plain,
    ( spl14_419
  <=> ~ r2_hidden(sK3,sK10(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_419])])).

fof(f3930,plain,
    ( ~ r2_hidden(sK3,sK10(sK3))
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f112,f3926,f326])).

fof(f4069,plain,
    ( spl14_416
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3928,f3925,f4067])).

fof(f3928,plain,
    ( r2_hidden(sK10(sK3),sK3)
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f112,f3926,f119])).

fof(f4031,plain,
    ( ~ spl14_415
    | ~ spl14_26
    | spl14_399 ),
    inference(avatar_split_clause,[],[f3855,f3848,f232,f4029])).

fof(f4029,plain,
    ( spl14_415
  <=> ~ r2_hidden(sK10(sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_415])])).

fof(f3855,plain,
    ( ~ r2_hidden(sK10(sK2),sK3)
    | ~ spl14_26
    | ~ spl14_399 ),
    inference(unit_resulting_resolution,[],[f112,f233,f3849,f344])).

fof(f4024,plain,
    ( ~ spl14_413
    | spl14_399 ),
    inference(avatar_split_clause,[],[f3853,f3848,f4022])).

fof(f4022,plain,
    ( spl14_413
  <=> ~ r2_hidden(sK2,sK10(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_413])])).

fof(f3853,plain,
    ( ~ r2_hidden(sK2,sK10(sK2))
    | ~ spl14_399 ),
    inference(unit_resulting_resolution,[],[f112,f3849,f326])).

fof(f4017,plain,
    ( spl14_410
    | spl14_399 ),
    inference(avatar_split_clause,[],[f3851,f3848,f4015])).

fof(f3851,plain,
    ( r2_hidden(sK10(sK2),sK2)
    | ~ spl14_399 ),
    inference(unit_resulting_resolution,[],[f112,f3849,f119])).

fof(f4006,plain,
    ( ~ spl14_409
    | spl14_405 ),
    inference(avatar_split_clause,[],[f3934,f3925,f4004])).

fof(f4004,plain,
    ( spl14_409
  <=> ~ m1_subset_1(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_409])])).

fof(f3934,plain,
    ( ~ m1_subset_1(sK3,sK3)
    | ~ spl14_405 ),
    inference(unit_resulting_resolution,[],[f3926,f762])).

fof(f3958,plain,
    ( ~ spl14_407
    | ~ spl14_384 ),
    inference(avatar_split_clause,[],[f3895,f3492,f3956])).

fof(f3956,plain,
    ( spl14_407
  <=> ~ r1_xboole_0(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_407])])).

fof(f3895,plain,
    ( ~ r1_xboole_0(sK3,sK3)
    | ~ spl14_384 ),
    inference(unit_resulting_resolution,[],[f3493,f3493,f115])).

fof(f3927,plain,
    ( ~ spl14_405
    | ~ spl14_384 ),
    inference(avatar_split_clause,[],[f3899,f3492,f3925])).

fof(f3899,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl14_384 ),
    inference(unit_resulting_resolution,[],[f3493,f124])).

fof(f3889,plain,
    ( ~ spl14_403
    | spl14_399 ),
    inference(avatar_split_clause,[],[f3856,f3848,f3887])).

fof(f3887,plain,
    ( spl14_403
  <=> ~ m1_subset_1(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_403])])).

fof(f3856,plain,
    ( ~ m1_subset_1(sK2,sK2)
    | ~ spl14_399 ),
    inference(unit_resulting_resolution,[],[f3849,f762])).

fof(f3876,plain,
    ( ~ spl14_401
    | ~ spl14_378 ),
    inference(avatar_split_clause,[],[f3819,f3464,f3874])).

fof(f3874,plain,
    ( spl14_401
  <=> ~ r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_401])])).

fof(f3819,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl14_378 ),
    inference(unit_resulting_resolution,[],[f3465,f3465,f115])).

fof(f3850,plain,
    ( ~ spl14_399
    | ~ spl14_378 ),
    inference(avatar_split_clause,[],[f3823,f3464,f3848])).

fof(f3823,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ spl14_378 ),
    inference(unit_resulting_resolution,[],[f3465,f124])).

fof(f3803,plain,
    ( ~ spl14_397
    | ~ spl14_340
    | spl14_377 ),
    inference(avatar_split_clause,[],[f3567,f3424,f2995,f3801])).

fof(f3801,plain,
    ( spl14_397
  <=> ~ r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_397])])).

fof(f2995,plain,
    ( spl14_340
  <=> k1_xboole_0 = sK10(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_340])])).

fof(f3424,plain,
    ( spl14_377
  <=> ~ r2_hidden(sK10(k1_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_377])])).

fof(f3567,plain,
    ( ~ r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_340
    | ~ spl14_377 ),
    inference(backward_demodulation,[],[f2996,f3425])).

fof(f3425,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_377 ),
    inference(avatar_component_clause,[],[f3424])).

fof(f2996,plain,
    ( k1_xboole_0 = sK10(k1_xboole_0)
    | ~ spl14_340 ),
    inference(avatar_component_clause,[],[f2995])).

fof(f3790,plain,
    ( spl14_278
    | ~ spl14_395
    | ~ spl14_302 ),
    inference(avatar_split_clause,[],[f3065,f2446,f3788,f2111])).

fof(f3788,plain,
    ( spl14_395
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_395])])).

fof(f2446,plain,
    ( spl14_302
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_302])])).

fof(f3065,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0)
    | ~ spl14_302 ),
    inference(resolution,[],[f2447,f326])).

fof(f2447,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_302 ),
    inference(avatar_component_clause,[],[f2446])).

fof(f3762,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3761])).

fof(f3761,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(subsumption_resolution,[],[f3688,f3609])).

fof(f3609,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl14_278
    | ~ spl14_286 ),
    inference(unit_resulting_resolution,[],[f3608,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | r2_hidden(sK11(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f3608,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286 ),
    inference(forward_demodulation,[],[f3601,f2235])).

fof(f2235,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_286 ),
    inference(avatar_component_clause,[],[f2234])).

fof(f2234,plain,
    ( spl14_286
  <=> k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_286])])).

fof(f3601,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f112,f2112,f127])).

fof(f3688,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2304,f2304,f115])).

fof(f2304,plain,
    ( r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_292 ),
    inference(avatar_component_clause,[],[f2303])).

fof(f2303,plain,
    ( spl14_292
  <=> r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_292])])).

fof(f3760,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3759])).

fof(f3759,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(subsumption_resolution,[],[f3692,f3609])).

fof(f3692,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2304,f2304,f115])).

fof(f3758,plain,
    ( ~ spl14_278
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3757])).

fof(f3757,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_292 ),
    inference(subsumption_resolution,[],[f3697,f2112])).

fof(f3697,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2304,f124])).

fof(f3756,plain,
    ( ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3755])).

fof(f3755,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(subsumption_resolution,[],[f3700,f2385])).

fof(f2385,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_298 ),
    inference(avatar_component_clause,[],[f2384])).

fof(f2384,plain,
    ( spl14_298
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_298])])).

fof(f3700,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2112,f2304,f127])).

fof(f3754,plain,
    ( ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3753])).

fof(f3753,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(subsumption_resolution,[],[f3701,f2112])).

fof(f3701,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(unit_resulting_resolution,[],[f2385,f2304,f127])).

fof(f3752,plain,
    ( ~ spl14_280
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3751])).

fof(f3751,plain,
    ( $false
    | ~ spl14_280
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(subsumption_resolution,[],[f3709,f2385])).

fof(f3709,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_280
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2133,f2304,f785])).

fof(f2133,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_280 ),
    inference(avatar_component_clause,[],[f2132])).

fof(f2132,plain,
    ( spl14_280
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_280])])).

fof(f3750,plain,
    ( ~ spl14_292
    | ~ spl14_298
    | ~ spl14_340 ),
    inference(avatar_contradiction_clause,[],[f3749])).

fof(f3749,plain,
    ( $false
    | ~ spl14_292
    | ~ spl14_298
    | ~ spl14_340 ),
    inference(subsumption_resolution,[],[f3748,f2385])).

fof(f3748,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_292
    | ~ spl14_340 ),
    inference(forward_demodulation,[],[f3710,f2996])).

fof(f3710,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f112,f2304,f785])).

fof(f3747,plain,
    ( ~ spl14_280
    | ~ spl14_286
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3746])).

fof(f3746,plain,
    ( $false
    | ~ spl14_280
    | ~ spl14_286
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(subsumption_resolution,[],[f3745,f2385])).

fof(f3745,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_280
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(forward_demodulation,[],[f3715,f2235])).

fof(f3715,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_280
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2133,f2304,f981])).

fof(f981,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X9,X7)
      | ~ m1_subset_1(X8,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(sK10(k1_zfmisc_1(X8)))) ) ),
    inference(resolution,[],[f791,f124])).

fof(f791,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK10(k1_zfmisc_1(X1))))
      | ~ m1_subset_1(X1,X0) ) ),
    inference(resolution,[],[f789,f119])).

fof(f789,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(X0)))) ) ),
    inference(subsumption_resolution,[],[f787,f127])).

fof(f787,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(sK10(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK10(k1_zfmisc_1(X0))))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f771,f126])).

fof(f771,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK10(k1_zfmisc_1(X0)))
      | v1_xboole_0(sK10(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f769,f119])).

fof(f769,plain,(
    ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f112,f765])).

fof(f3744,plain,
    ( ~ spl14_286
    | ~ spl14_292
    | ~ spl14_298
    | ~ spl14_340 ),
    inference(avatar_contradiction_clause,[],[f3743])).

fof(f3743,plain,
    ( $false
    | ~ spl14_286
    | ~ spl14_292
    | ~ spl14_298
    | ~ spl14_340 ),
    inference(subsumption_resolution,[],[f3742,f2385])).

fof(f3742,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_286
    | ~ spl14_292
    | ~ spl14_340 ),
    inference(forward_demodulation,[],[f3741,f2235])).

fof(f3741,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_292
    | ~ spl14_340 ),
    inference(forward_demodulation,[],[f3716,f2996])).

fof(f3716,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_xboole_0)))))
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f112,f2304,f981])).

fof(f3740,plain,
    ( ~ spl14_278
    | ~ spl14_280
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3719])).

fof(f3719,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_280
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2133,f3608,f2304,f1729])).

fof(f3739,plain,
    ( ~ spl14_280
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3712])).

fof(f3712,plain,
    ( $false
    | ~ spl14_280
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(unit_resulting_resolution,[],[f2133,f2385,f2304,f785])).

fof(f3738,plain,
    ( ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(avatar_contradiction_clause,[],[f3702])).

fof(f3702,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_292
    | ~ spl14_298 ),
    inference(unit_resulting_resolution,[],[f2112,f2385,f2304,f127])).

fof(f3737,plain,
    ( ~ spl14_278
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3698])).

fof(f3698,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2112,f2304,f124])).

fof(f3736,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3693])).

fof(f3693,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f3609,f2304,f2304,f115])).

fof(f3735,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3689])).

fof(f3689,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f3609,f2304,f2304,f115])).

fof(f3734,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3685])).

fof(f3685,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f3608,f2304])).

fof(f3733,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(avatar_contradiction_clause,[],[f3720])).

fof(f3720,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_292 ),
    inference(resolution,[],[f2304,f3608])).

fof(f3684,plain,
    ( ~ spl14_393
    | ~ spl14_302 ),
    inference(avatar_split_clause,[],[f3064,f2446,f3682])).

fof(f3682,plain,
    ( spl14_393
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_393])])).

fof(f3064,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_xboole_0)
    | ~ spl14_302 ),
    inference(resolution,[],[f2447,f117])).

fof(f3659,plain,
    ( spl14_390
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_192
    | ~ spl14_304 ),
    inference(avatar_split_clause,[],[f2674,f2456,f1036,f199,f178,f150,f143,f136,f3657])).

fof(f3657,plain,
    ( spl14_390
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_390])])).

fof(f2456,plain,
    ( spl14_304
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_304])])).

fof(f2674,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))),sK3)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_192
    | ~ spl14_304 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f1037,f2457,f108])).

fof(f2457,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)))
    | ~ spl14_304 ),
    inference(avatar_component_clause,[],[f2456])).

fof(f3652,plain,
    ( spl14_280
    | ~ spl14_340 ),
    inference(avatar_split_clause,[],[f3643,f2995,f2132])).

fof(f3643,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_340 ),
    inference(superposition,[],[f112,f2996])).

fof(f3645,plain,
    ( spl14_281
    | ~ spl14_340 ),
    inference(avatar_contradiction_clause,[],[f3644])).

fof(f3644,plain,
    ( $false
    | ~ spl14_281
    | ~ spl14_340 ),
    inference(subsumption_resolution,[],[f3643,f2136])).

fof(f2136,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_281 ),
    inference(avatar_component_clause,[],[f2135])).

fof(f2135,plain,
    ( spl14_281
  <=> ~ m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_281])])).

fof(f3640,plain,
    ( spl14_282
    | ~ spl14_332
    | ~ spl14_340 ),
    inference(avatar_split_clause,[],[f3583,f2995,f2817,f2139])).

fof(f2139,plain,
    ( spl14_282
  <=> r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_282])])).

fof(f2817,plain,
    ( spl14_332
  <=> r1_xboole_0(sK10(k1_xboole_0),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_332])])).

fof(f3583,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_332
    | ~ spl14_340 ),
    inference(forward_demodulation,[],[f2818,f2996])).

fof(f2818,plain,
    ( r1_xboole_0(sK10(k1_xboole_0),sK10(k1_xboole_0))
    | ~ spl14_332 ),
    inference(avatar_component_clause,[],[f2817])).

fof(f3624,plain,
    ( spl14_388
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_190
    | ~ spl14_300 ),
    inference(avatar_split_clause,[],[f2582,f2391,f1029,f192,f178,f150,f143,f136,f3622])).

fof(f3622,plain,
    ( spl14_388
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_388])])).

fof(f2391,plain,
    ( spl14_300
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_300])])).

fof(f2582,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_190
    | ~ spl14_300 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f1030,f2392,f108])).

fof(f2392,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)))
    | ~ spl14_300 ),
    inference(avatar_component_clause,[],[f2391])).

fof(f3593,plain,
    ( spl14_278
    | ~ spl14_326
    | ~ spl14_340 ),
    inference(avatar_split_clause,[],[f3527,f2995,f2775,f2111])).

fof(f2775,plain,
    ( spl14_326
  <=> v1_xboole_0(sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_326])])).

fof(f3527,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_326
    | ~ spl14_340 ),
    inference(backward_demodulation,[],[f2996,f2776])).

fof(f2776,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl14_326 ),
    inference(avatar_component_clause,[],[f2775])).

fof(f3524,plain,
    ( spl14_333
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3523])).

fof(f3523,plain,
    ( $false
    | ~ spl14_333
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3185,f3504])).

fof(f3504,plain,
    ( ~ r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_387 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f3503,plain,
    ( spl14_387
  <=> ~ r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_387])])).

fof(f3185,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(resolution,[],[f2821,f113])).

fof(f2821,plain,
    ( ~ r1_xboole_0(sK10(k1_xboole_0),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(avatar_component_clause,[],[f2820])).

fof(f2820,plain,
    ( spl14_333
  <=> ~ r1_xboole_0(sK10(k1_xboole_0),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_333])])).

fof(f3522,plain,
    ( spl14_333
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3521])).

fof(f3521,plain,
    ( $false
    | ~ spl14_333
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3184,f3504])).

fof(f3184,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(resolution,[],[f2821,f114])).

fof(f3520,plain,
    ( spl14_333
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3519])).

fof(f3519,plain,
    ( $false
    | ~ spl14_333
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3181,f3504])).

fof(f3181,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(unit_resulting_resolution,[],[f2821,f114])).

fof(f3518,plain,
    ( spl14_333
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3517])).

fof(f3517,plain,
    ( $false
    | ~ spl14_333
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3182,f3504])).

fof(f3182,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(unit_resulting_resolution,[],[f2821,f113])).

fof(f3516,plain,
    ( ~ spl14_326
    | spl14_341 ),
    inference(avatar_contradiction_clause,[],[f3515])).

fof(f3515,plain,
    ( $false
    | ~ spl14_326
    | ~ spl14_341 ),
    inference(subsumption_resolution,[],[f3029,f2776])).

fof(f3029,plain,
    ( ~ v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl14_341 ),
    inference(unit_resulting_resolution,[],[f2993,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t6_boole)).

fof(f2993,plain,
    ( k1_xboole_0 != sK10(k1_xboole_0)
    | ~ spl14_341 ),
    inference(avatar_component_clause,[],[f2992])).

fof(f2992,plain,
    ( spl14_341
  <=> k1_xboole_0 != sK10(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_341])])).

fof(f3514,plain,
    ( spl14_341
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3513])).

fof(f3513,plain,
    ( $false
    | ~ spl14_341
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3034,f3504])).

fof(f3034,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_341 ),
    inference(unit_resulting_resolution,[],[f112,f2993,f1730])).

fof(f1730,plain,(
    ! [X14,X15] :
      ( r2_hidden(sK11(X15,X15),X15)
      | ~ m1_subset_1(X14,X15)
      | k1_xboole_0 = X15 ) ),
    inference(resolution,[],[f1723,f98])).

fof(f3512,plain,
    ( ~ spl14_326
    | ~ spl14_334 ),
    inference(avatar_contradiction_clause,[],[f3511])).

fof(f3511,plain,
    ( $false
    | ~ spl14_326
    | ~ spl14_334 ),
    inference(subsumption_resolution,[],[f2776,f3213])).

fof(f3213,plain,
    ( ~ v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl14_334 ),
    inference(unit_resulting_resolution,[],[f2838,f124])).

fof(f2838,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_334 ),
    inference(avatar_component_clause,[],[f2837])).

fof(f2837,plain,
    ( spl14_334
  <=> r2_hidden(sK10(sK10(k1_xboole_0)),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_334])])).

fof(f3510,plain,
    ( ~ spl14_334
    | spl14_387 ),
    inference(avatar_contradiction_clause,[],[f3509])).

fof(f3509,plain,
    ( $false
    | ~ spl14_334
    | ~ spl14_387 ),
    inference(subsumption_resolution,[],[f3504,f3220])).

fof(f3220,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_334 ),
    inference(unit_resulting_resolution,[],[f112,f2838,f1729])).

fof(f3508,plain,
    ( spl14_386
    | spl14_327 ),
    inference(avatar_split_clause,[],[f3008,f2772,f3506])).

fof(f3506,plain,
    ( spl14_386
  <=> r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_386])])).

fof(f2772,plain,
    ( spl14_327
  <=> ~ v1_xboole_0(sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_327])])).

fof(f3008,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f112,f2773,f1723])).

fof(f2773,plain,
    ( ~ v1_xboole_0(sK10(k1_xboole_0))
    | ~ spl14_327 ),
    inference(avatar_component_clause,[],[f2772])).

fof(f3494,plain,
    ( spl14_384
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_188
    | ~ spl14_296 ),
    inference(avatar_split_clause,[],[f2559,f2354,f1022,f199,f178,f150,f143,f136,f3492])).

fof(f2354,plain,
    ( spl14_296
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).

fof(f2559,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))),sK3)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18
    | ~ spl14_188
    | ~ spl14_296 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f1023,f2355,f108])).

fof(f2355,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))))
    | ~ spl14_296 ),
    inference(avatar_component_clause,[],[f2354])).

fof(f3484,plain,
    ( ~ spl14_383
    | spl14_381 ),
    inference(avatar_split_clause,[],[f3475,f3471,f3482])).

fof(f3482,plain,
    ( spl14_383
  <=> ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_383])])).

fof(f3471,plain,
    ( spl14_381
  <=> ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_381])])).

fof(f3475,plain,
    ( ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_381 ),
    inference(unit_resulting_resolution,[],[f3472,f118])).

fof(f3472,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_381 ),
    inference(avatar_component_clause,[],[f3471])).

fof(f3473,plain,
    ( ~ spl14_381
    | ~ spl14_258
    | ~ spl14_278 ),
    inference(avatar_split_clause,[],[f3446,f2111,f1851,f3471])).

fof(f1851,plain,
    ( spl14_258
  <=> r2_hidden(sK10(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_258])])).

fof(f3446,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_258
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f1852,f2553])).

fof(f2553,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl14_278 ),
    inference(resolution,[],[f2112,f127])).

fof(f1852,plain,
    ( r2_hidden(sK10(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1))
    | ~ spl14_258 ),
    inference(avatar_component_clause,[],[f1851])).

fof(f3466,plain,
    ( spl14_378
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_182
    | ~ spl14_294 ),
    inference(avatar_split_clause,[],[f2522,f2316,f1001,f192,f178,f150,f143,f136,f3464])).

fof(f2316,plain,
    ( spl14_294
  <=> r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_294])])).

fof(f2522,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))),sK2)
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16
    | ~ spl14_182
    | ~ spl14_294 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f1002,f2317,f108])).

fof(f2317,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))))
    | ~ spl14_294 ),
    inference(avatar_component_clause,[],[f2316])).

fof(f3426,plain,
    ( ~ spl14_377
    | spl14_349 ),
    inference(avatar_split_clause,[],[f3240,f3237,f3424])).

fof(f3237,plain,
    ( spl14_349
  <=> ~ m1_subset_1(sK10(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_349])])).

fof(f3240,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),sK10(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_349 ),
    inference(unit_resulting_resolution,[],[f112,f3238,f126])).

fof(f3238,plain,
    ( ~ m1_subset_1(sK10(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_349 ),
    inference(avatar_component_clause,[],[f3237])).

fof(f3412,plain,
    ( spl14_374
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_166 ),
    inference(avatar_split_clause,[],[f949,f902,f178,f150,f143,f136,f3410])).

fof(f3410,plain,
    ( spl14_374
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_374])])).

fof(f902,plain,
    ( spl14_166
  <=> m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1))),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_166])])).

fof(f949,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1)))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_166 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f903,f125])).

fof(f903,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_166 ),
    inference(avatar_component_clause,[],[f902])).

fof(f3405,plain,
    ( ~ spl14_373
    | spl14_341 ),
    inference(avatar_split_clause,[],[f3031,f2992,f3403])).

fof(f3403,plain,
    ( spl14_373
  <=> ~ r2_hidden(sK10(k1_xboole_0),k1_zfmisc_1(sK10(sK10(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_373])])).

fof(f3031,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),k1_zfmisc_1(sK10(sK10(k1_xboole_0))))
    | ~ spl14_341 ),
    inference(unit_resulting_resolution,[],[f112,f2993,f813])).

fof(f813,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X4,k1_zfmisc_1(X3))
      | k1_xboole_0 = X4
      | ~ m1_subset_1(X3,X4) ) ),
    inference(resolution,[],[f786,f118])).

fof(f786,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(X11))
      | ~ m1_subset_1(X11,X10)
      | k1_xboole_0 = X10 ) ),
    inference(resolution,[],[f770,f98])).

fof(f3384,plain,
    ( ~ spl14_371
    | ~ spl14_308
    | spl14_325 ),
    inference(avatar_split_clause,[],[f3111,f2769,f2524,f3382])).

fof(f3382,plain,
    ( spl14_371
  <=> ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_371])])).

fof(f2524,plain,
    ( spl14_308
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_308])])).

fof(f2769,plain,
    ( spl14_325
  <=> ~ m1_subset_1(k1_xboole_0,sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_325])])).

fof(f3111,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_308
    | ~ spl14_325 ),
    inference(unit_resulting_resolution,[],[f2770,f2525,f126])).

fof(f2525,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_308 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2770,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK10(k1_xboole_0))
    | ~ spl14_325 ),
    inference(avatar_component_clause,[],[f2769])).

fof(f3360,plain,
    ( ~ spl14_369
    | ~ spl14_308 ),
    inference(avatar_split_clause,[],[f3104,f2524,f3358])).

fof(f3358,plain,
    ( spl14_369
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_369])])).

fof(f3104,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_308 ),
    inference(unit_resulting_resolution,[],[f2525,f2525,f115])).

fof(f3353,plain,
    ( ~ spl14_367
    | spl14_327 ),
    inference(avatar_split_clause,[],[f3003,f2772,f3351])).

fof(f3351,plain,
    ( spl14_367
  <=> ~ m1_subset_1(sK10(k1_xboole_0),k1_zfmisc_1(sK10(sK10(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_367])])).

fof(f3003,plain,
    ( ~ m1_subset_1(sK10(k1_xboole_0),k1_zfmisc_1(sK10(sK10(k1_xboole_0))))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f112,f2773,f770])).

fof(f3325,plain,
    ( ~ spl14_365
    | spl14_357 ),
    inference(avatar_split_clause,[],[f3301,f3281,f3323])).

fof(f3323,plain,
    ( spl14_365
  <=> ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_365])])).

fof(f3281,plain,
    ( spl14_357
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_357])])).

fof(f3301,plain,
    ( ~ r2_hidden(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_357 ),
    inference(unit_resulting_resolution,[],[f3282,f118])).

fof(f3282,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_357 ),
    inference(avatar_component_clause,[],[f3281])).

fof(f3318,plain,
    ( ~ spl14_363
    | ~ spl14_298
    | ~ spl14_308
    | spl14_315 ),
    inference(avatar_split_clause,[],[f3113,f2590,f2524,f2384,f3316])).

fof(f3316,plain,
    ( spl14_363
  <=> ~ r1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_363])])).

fof(f2590,plain,
    ( spl14_315
  <=> ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_315])])).

fof(f3113,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_298
    | ~ spl14_308
    | ~ spl14_315 ),
    inference(unit_resulting_resolution,[],[f2591,f2385,f2525,f344])).

fof(f2591,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_315 ),
    inference(avatar_component_clause,[],[f2590])).

fof(f3297,plain,
    ( ~ spl14_361
    | spl14_355 ),
    inference(avatar_split_clause,[],[f3274,f3270,f3295])).

fof(f3295,plain,
    ( spl14_361
  <=> ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_361])])).

fof(f3270,plain,
    ( spl14_355
  <=> ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_355])])).

fof(f3274,plain,
    ( ~ r2_hidden(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_355 ),
    inference(unit_resulting_resolution,[],[f3271,f118])).

fof(f3271,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_355 ),
    inference(avatar_component_clause,[],[f3270])).

fof(f3290,plain,
    ( ~ spl14_359
    | ~ spl14_302
    | ~ spl14_308 ),
    inference(avatar_split_clause,[],[f3103,f2524,f2446,f3288])).

fof(f3288,plain,
    ( spl14_359
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_359])])).

fof(f3103,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_302
    | ~ spl14_308 ),
    inference(unit_resulting_resolution,[],[f2447,f2525,f115])).

fof(f3283,plain,
    ( ~ spl14_357
    | ~ spl14_302
    | spl14_325 ),
    inference(avatar_split_clause,[],[f3052,f2769,f2446,f3281])).

fof(f3052,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_302
    | ~ spl14_325 ),
    inference(unit_resulting_resolution,[],[f2770,f2447,f126])).

fof(f3272,plain,
    ( ~ spl14_355
    | ~ spl14_286
    | ~ spl14_290
    | ~ spl14_308 ),
    inference(avatar_split_clause,[],[f3134,f2524,f2293,f2234,f3270])).

fof(f2293,plain,
    ( spl14_290
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_290])])).

fof(f3134,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_286
    | ~ spl14_290
    | ~ spl14_308 ),
    inference(forward_demodulation,[],[f3118,f2235])).

fof(f3118,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(sK10(k1_xboole_0)),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_290
    | ~ spl14_308 ),
    inference(unit_resulting_resolution,[],[f2294,f2525,f981])).

fof(f2294,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_290 ),
    inference(avatar_component_clause,[],[f2293])).

fof(f3261,plain,
    ( ~ spl14_353
    | spl14_327 ),
    inference(avatar_split_clause,[],[f3000,f2772,f3259])).

fof(f3259,plain,
    ( spl14_353
  <=> ~ r2_hidden(sK10(k1_xboole_0),sK10(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_353])])).

fof(f3000,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),sK10(sK10(k1_xboole_0)))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f112,f2773,f326])).

fof(f3252,plain,
    ( ~ spl14_351
    | spl14_349 ),
    inference(avatar_split_clause,[],[f3241,f3237,f3250])).

fof(f3250,plain,
    ( spl14_351
  <=> ~ r2_hidden(sK10(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_351])])).

fof(f3241,plain,
    ( ~ r2_hidden(sK10(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_349 ),
    inference(unit_resulting_resolution,[],[f3238,f118])).

fof(f3239,plain,
    ( ~ spl14_349
    | ~ spl14_278
    | ~ spl14_334 ),
    inference(avatar_split_clause,[],[f3214,f2837,f2111,f3237])).

fof(f3214,plain,
    ( ~ m1_subset_1(sK10(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_334 ),
    inference(unit_resulting_resolution,[],[f2112,f2838,f127])).

fof(f3205,plain,
    ( ~ spl14_347
    | spl14_325 ),
    inference(avatar_split_clause,[],[f2798,f2769,f3203])).

fof(f3203,plain,
    ( spl14_347
  <=> ~ r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(sK10(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_347])])).

fof(f2798,plain,
    ( ~ r2_hidden(k1_xboole_0,sK10(k1_zfmisc_1(sK10(k1_xboole_0))))
    | ~ spl14_325 ),
    inference(unit_resulting_resolution,[],[f112,f2770,f126])).

fof(f3145,plain,
    ( ~ spl14_345
    | ~ spl14_308 ),
    inference(avatar_split_clause,[],[f3109,f2524,f3143])).

fof(f3143,plain,
    ( spl14_345
  <=> ~ v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_345])])).

fof(f3109,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_308 ),
    inference(unit_resulting_resolution,[],[f2525,f124])).

fof(f3028,plain,
    ( spl14_342
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f656,f572,f564,f251,f157,f150,f3026])).

fof(f157,plain,
    ( spl14_6
  <=> v7_waybel_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f251,plain,
    ( spl14_30
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_30])])).

fof(f564,plain,
    ( spl14_102
  <=> m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_102])])).

fof(f572,plain,
    ( spl14_104
  <=> m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_104])])).

fof(f656,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f573,f103])).

fof(f103,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X5,sK7(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ( ! [X3] :
                ( ~ r1_orders_2(X0,sK6(X0),X3)
                | ~ r1_orders_2(X0,sK5(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ( r1_orders_2(X0,X5,sK7(X0,X4,X5))
                    & r1_orders_2(X0,X4,sK7(X0,X4,X5))
                    & m1_subset_1(sK7(X0,X4,X5),u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f71,f74,f73,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ! [X3] :
                ( ~ r1_orders_2(X0,X2,X3)
                | ~ r1_orders_2(X0,sK5(X0),X3)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r1_orders_2(X0,X2,X3)
              | ~ r1_orders_2(X0,X1,X3)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ! [X3] :
            ( ~ r1_orders_2(X0,sK6(X0),X3)
            | ~ r1_orders_2(X0,X1,X3)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f74,plain,(
    ! [X5,X4,X0] :
      ( ? [X6] :
          ( r1_orders_2(X0,X5,X6)
          & r1_orders_2(X0,X4,X6)
          & m1_subset_1(X6,u1_struct_0(X0)) )
     => ( r1_orders_2(X0,X5,sK7(X0,X4,X5))
        & r1_orders_2(X0,X4,sK7(X0,X4,X5))
        & m1_subset_1(sK7(X0,X4,X5),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X4] :
              ( ! [X5] :
                  ( ? [X6] :
                      ( r1_orders_2(X0,X5,X6)
                      & r1_orders_2(X0,X4,X6)
                      & m1_subset_1(X6,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v7_waybel_0(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( ! [X3] :
                      ( ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( ? [X3] :
                      ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v7_waybel_0(X0) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ? [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    & r1_orders_2(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',d5_yellow_6)).

fof(f573,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl14_104 ),
    inference(avatar_component_clause,[],[f572])).

fof(f565,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_102 ),
    inference(avatar_component_clause,[],[f564])).

fof(f158,plain,
    ( v7_waybel_0(sK1)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f157])).

fof(f252,plain,
    ( l1_orders_2(sK1)
    | ~ spl14_30 ),
    inference(avatar_component_clause,[],[f251])).

fof(f2997,plain,
    ( spl14_340
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_326 ),
    inference(avatar_split_clause,[],[f2856,f2775,f2234,f2111,f2995])).

fof(f2856,plain,
    ( k1_xboole_0 = sK10(k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_326 ),
    inference(unit_resulting_resolution,[],[f112,f2557,f2776,f1728])).

fof(f1728,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(X10)
      | r2_hidden(sK11(X9,X9),X9)
      | X9 = X10
      | ~ m1_subset_1(X8,X9) ) ),
    inference(resolution,[],[f1723,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t8_boole)).

fof(f2557,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286 ),
    inference(forward_demodulation,[],[f2550,f2235])).

fof(f2550,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f112,f2112,f127])).

fof(f2974,plain,
    ( spl14_338
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f654,f572,f564,f251,f157,f150,f2972])).

fof(f654,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f565,f103])).

fof(f2967,plain,
    ( spl14_302
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_308
    | ~ spl14_326 ),
    inference(avatar_split_clause,[],[f2943,f2775,f2524,f2234,f2111,f2446])).

fof(f2943,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_308
    | ~ spl14_326 ),
    inference(forward_demodulation,[],[f2525,f2856])).

fof(f2932,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | spl14_293
    | ~ spl14_314
    | spl14_317 ),
    inference(avatar_contradiction_clause,[],[f2931])).

fof(f2931,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_293
    | ~ spl14_314
    | ~ spl14_317 ),
    inference(subsumption_resolution,[],[f2923,f2301])).

fof(f2301,plain,
    ( ~ r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_293 ),
    inference(avatar_component_clause,[],[f2300])).

fof(f2300,plain,
    ( spl14_293
  <=> ~ r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_293])])).

fof(f2923,plain,
    ( r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_314
    | ~ spl14_317 ),
    inference(backward_demodulation,[],[f2910,f2717])).

fof(f2717,plain,
    ( r2_hidden(sK11(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_317 ),
    inference(resolution,[],[f2697,f113])).

fof(f2697,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_317 ),
    inference(avatar_component_clause,[],[f2696])).

fof(f2696,plain,
    ( spl14_317
  <=> ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_317])])).

fof(f2910,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_xboole_0
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_314 ),
    inference(unit_resulting_resolution,[],[f112,f2557,f2594,f1728])).

fof(f2594,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_314 ),
    inference(avatar_component_clause,[],[f2593])).

fof(f2593,plain,
    ( spl14_314
  <=> v1_xboole_0(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_314])])).

fof(f2930,plain,
    ( ~ spl14_278
    | ~ spl14_282
    | ~ spl14_286
    | ~ spl14_314
    | spl14_317 ),
    inference(avatar_contradiction_clause,[],[f2929])).

fof(f2929,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_282
    | ~ spl14_286
    | ~ spl14_314
    | ~ spl14_317 ),
    inference(subsumption_resolution,[],[f2921,f2140])).

fof(f2140,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_282 ),
    inference(avatar_component_clause,[],[f2139])).

fof(f2921,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_314
    | ~ spl14_317 ),
    inference(backward_demodulation,[],[f2910,f2697])).

fof(f2928,plain,
    ( ~ spl14_278
    | spl14_281
    | ~ spl14_286
    | ~ spl14_298
    | ~ spl14_314 ),
    inference(avatar_contradiction_clause,[],[f2927])).

fof(f2927,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_281
    | ~ spl14_286
    | ~ spl14_298
    | ~ spl14_314 ),
    inference(subsumption_resolution,[],[f2918,f2136])).

fof(f2918,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_298
    | ~ spl14_314 ),
    inference(backward_demodulation,[],[f2910,f2385])).

fof(f2901,plain,
    ( spl14_314
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_298
    | spl14_309
    | ~ spl14_326 ),
    inference(avatar_split_clause,[],[f2898,f2775,f2527,f2384,f2234,f2111,f2593])).

fof(f2527,plain,
    ( spl14_309
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_309])])).

fof(f2898,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_298
    | ~ spl14_309
    | ~ spl14_326 ),
    inference(subsumption_resolution,[],[f2897,f2385])).

fof(f2897,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_309
    | ~ spl14_326 ),
    inference(forward_demodulation,[],[f2896,f2856])).

fof(f2896,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_309
    | ~ spl14_326 ),
    inference(forward_demodulation,[],[f2684,f2856])).

fof(f2684,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_309 ),
    inference(resolution,[],[f2528,f119])).

fof(f2528,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_309 ),
    inference(avatar_component_clause,[],[f2527])).

fof(f2886,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | spl14_293
    | ~ spl14_326
    | spl14_333 ),
    inference(avatar_contradiction_clause,[],[f2885])).

fof(f2885,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_293
    | ~ spl14_326
    | ~ spl14_333 ),
    inference(subsumption_resolution,[],[f2877,f2301])).

fof(f2877,plain,
    ( r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_326
    | ~ spl14_333 ),
    inference(backward_demodulation,[],[f2856,f2831])).

fof(f2831,plain,
    ( r2_hidden(sK11(sK10(k1_xboole_0),sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_333 ),
    inference(resolution,[],[f2821,f113])).

fof(f2884,plain,
    ( ~ spl14_278
    | ~ spl14_282
    | ~ spl14_286
    | ~ spl14_326
    | spl14_333 ),
    inference(avatar_contradiction_clause,[],[f2883])).

fof(f2883,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_282
    | ~ spl14_286
    | ~ spl14_326
    | ~ spl14_333 ),
    inference(subsumption_resolution,[],[f2876,f2140])).

fof(f2876,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_326
    | ~ spl14_333 ),
    inference(backward_demodulation,[],[f2856,f2821])).

fof(f2882,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | ~ spl14_302
    | spl14_309
    | ~ spl14_326 ),
    inference(avatar_contradiction_clause,[],[f2881])).

fof(f2881,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_302
    | ~ spl14_309
    | ~ spl14_326 ),
    inference(subsumption_resolution,[],[f2868,f2447])).

fof(f2868,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_309
    | ~ spl14_326 ),
    inference(backward_demodulation,[],[f2856,f2528])).

fof(f2880,plain,
    ( ~ spl14_278
    | ~ spl14_286
    | spl14_291
    | ~ spl14_298
    | ~ spl14_326 ),
    inference(avatar_contradiction_clause,[],[f2879])).

fof(f2879,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_291
    | ~ spl14_298
    | ~ spl14_326 ),
    inference(subsumption_resolution,[],[f2865,f2385])).

fof(f2865,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278
    | ~ spl14_286
    | ~ spl14_291
    | ~ spl14_326 ),
    inference(backward_demodulation,[],[f2856,f2297])).

fof(f2297,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_291 ),
    inference(avatar_component_clause,[],[f2296])).

fof(f2296,plain,
    ( spl14_291
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_291])])).

fof(f2846,plain,
    ( spl14_336
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f628,f572,f251,f157,f150,f2844])).

fof(f628,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f573,f102])).

fof(f102,plain,(
    ! [X4,X0,X5] :
      ( r1_orders_2(X0,X4,sK7(X0,X4,X5))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f2839,plain,
    ( spl14_334
    | spl14_327 ),
    inference(avatar_split_clause,[],[f2778,f2772,f2837])).

fof(f2778,plain,
    ( r2_hidden(sK10(sK10(k1_xboole_0)),sK10(k1_xboole_0))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f112,f2773,f119])).

fof(f2822,plain,
    ( ~ spl14_333
    | spl14_327 ),
    inference(avatar_split_clause,[],[f2788,f2772,f2820])).

fof(f2788,plain,
    ( ~ r1_xboole_0(sK10(k1_xboole_0),sK10(k1_xboole_0))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f112,f2773,f1715])).

fof(f2815,plain,
    ( ~ spl14_331
    | spl14_327 ),
    inference(avatar_split_clause,[],[f2783,f2772,f2813])).

fof(f2813,plain,
    ( spl14_331
  <=> ~ m1_subset_1(sK10(k1_xboole_0),sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_331])])).

fof(f2783,plain,
    ( ~ m1_subset_1(sK10(k1_xboole_0),sK10(k1_xboole_0))
    | ~ spl14_327 ),
    inference(unit_resulting_resolution,[],[f2773,f762])).

fof(f2808,plain,
    ( spl14_328
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f627,f572,f564,f251,f157,f150,f2806])).

fof(f627,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f573,f102])).

fof(f2777,plain,
    ( ~ spl14_325
    | spl14_326
    | spl14_289 ),
    inference(avatar_split_clause,[],[f2291,f2288,f2775,f2769])).

fof(f2288,plain,
    ( spl14_289
  <=> ~ r2_hidden(k1_xboole_0,sK10(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_289])])).

fof(f2291,plain,
    ( v1_xboole_0(sK10(k1_xboole_0))
    | ~ m1_subset_1(k1_xboole_0,sK10(k1_xboole_0))
    | ~ spl14_289 ),
    inference(resolution,[],[f2289,f119])).

fof(f2289,plain,
    ( ~ r2_hidden(k1_xboole_0,sK10(k1_xboole_0))
    | ~ spl14_289 ),
    inference(avatar_component_clause,[],[f2288])).

fof(f2751,plain,
    ( spl14_322
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f625,f572,f564,f251,f157,f150,f2749])).

fof(f625,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f565,f102])).

fof(f2712,plain,
    ( ~ spl14_321
    | ~ spl14_286
    | spl14_315 ),
    inference(avatar_split_clause,[],[f2622,f2590,f2234,f2710])).

fof(f2710,plain,
    ( spl14_321
  <=> ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_321])])).

fof(f2622,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_286
    | ~ spl14_315 ),
    inference(forward_demodulation,[],[f2621,f2235])).

fof(f2621,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl14_286
    | ~ spl14_315 ),
    inference(forward_demodulation,[],[f2607,f2235])).

fof(f2607,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(sK10(k1_zfmisc_1(sK10(k1_zfmisc_1(k1_xboole_0))))))
    | ~ spl14_315 ),
    inference(unit_resulting_resolution,[],[f112,f2591,f791])).

fof(f2705,plain,
    ( spl14_318
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f624,f564,f251,f157,f150,f2703])).

fof(f624,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f565,f102])).

fof(f2698,plain,
    ( ~ spl14_317
    | ~ spl14_298
    | spl14_315 ),
    inference(avatar_split_clause,[],[f2612,f2590,f2384,f2696])).

fof(f2612,plain,
    ( ~ r1_xboole_0(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_298
    | ~ spl14_315 ),
    inference(unit_resulting_resolution,[],[f2385,f2591,f1715])).

fof(f2595,plain,
    ( spl14_314
    | ~ spl14_298
    | spl14_303 ),
    inference(avatar_split_clause,[],[f2586,f2449,f2384,f2593])).

fof(f2449,plain,
    ( spl14_303
  <=> ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_303])])).

fof(f2586,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_298
    | ~ spl14_303 ),
    inference(unit_resulting_resolution,[],[f2450,f2385,f119])).

fof(f2450,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_303 ),
    inference(avatar_component_clause,[],[f2449])).

fof(f2545,plain,
    ( spl14_278
    | ~ spl14_286
    | ~ spl14_306 ),
    inference(avatar_split_clause,[],[f2544,f2495,f2234,f2111])).

fof(f2495,plain,
    ( spl14_306
  <=> v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_306])])).

fof(f2544,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_286
    | ~ spl14_306 ),
    inference(backward_demodulation,[],[f2235,f2496])).

fof(f2496,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_306 ),
    inference(avatar_component_clause,[],[f2495])).

fof(f2543,plain,
    ( spl14_312
    | ~ spl14_292 ),
    inference(avatar_split_clause,[],[f2464,f2303,f2541])).

fof(f2541,plain,
    ( spl14_312
  <=> m1_subset_1(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_312])])).

fof(f2464,plain,
    ( m1_subset_1(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2304,f118])).

fof(f2536,plain,
    ( ~ spl14_311
    | ~ spl14_292 ),
    inference(avatar_split_clause,[],[f2463,f2303,f2534])).

fof(f2534,plain,
    ( spl14_311
  <=> ~ r2_hidden(k1_xboole_0,sK11(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_311])])).

fof(f2463,plain,
    ( ~ r2_hidden(k1_xboole_0,sK11(k1_xboole_0,k1_xboole_0))
    | ~ spl14_292 ),
    inference(unit_resulting_resolution,[],[f2304,f117])).

fof(f2529,plain,
    ( ~ spl14_309
    | spl14_291 ),
    inference(avatar_split_clause,[],[f2360,f2296,f2527])).

fof(f2360,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_291 ),
    inference(unit_resulting_resolution,[],[f2297,f118])).

fof(f2500,plain,
    ( ~ spl14_307
    | spl14_287 ),
    inference(avatar_split_clause,[],[f2484,f2231,f2498])).

fof(f2498,plain,
    ( spl14_307
  <=> ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_307])])).

fof(f2231,plain,
    ( spl14_287
  <=> k1_xboole_0 != sK10(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_287])])).

fof(f2484,plain,
    ( ~ v1_xboole_0(sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_287 ),
    inference(unit_resulting_resolution,[],[f2232,f98])).

fof(f2232,plain,
    ( k1_xboole_0 != sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_287 ),
    inference(avatar_component_clause,[],[f2231])).

fof(f2458,plain,
    ( spl14_304
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f655,f572,f251,f157,f150,f2456])).

fof(f655,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f573,f103])).

fof(f2451,plain,
    ( ~ spl14_303
    | spl14_299 ),
    inference(avatar_split_clause,[],[f2442,f2381,f2449])).

fof(f2381,plain,
    ( spl14_299
  <=> ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_299])])).

fof(f2442,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_299 ),
    inference(unit_resulting_resolution,[],[f2382,f118])).

fof(f2382,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_299 ),
    inference(avatar_component_clause,[],[f2381])).

fof(f2393,plain,
    ( spl14_300
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f652,f564,f251,f157,f150,f2391])).

fof(f652,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f565,f103])).

fof(f2386,plain,
    ( spl14_298
    | ~ spl14_286 ),
    inference(avatar_split_clause,[],[f2379,f2234,f2384])).

fof(f2379,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_286 ),
    inference(superposition,[],[f112,f2235])).

fof(f2356,plain,
    ( spl14_296
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f622,f572,f251,f157,f150,f2354])).

fof(f622,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK3),sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f112,f102])).

fof(f2318,plain,
    ( spl14_294
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f621,f564,f251,f157,f150,f2316])).

fof(f621,plain,
    ( r1_orders_2(sK1,sK9(sK0,sK1,sK2),sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f112,f102])).

fof(f2311,plain,
    ( ~ spl14_278
    | ~ spl14_284 ),
    inference(avatar_contradiction_clause,[],[f2310])).

fof(f2310,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_284 ),
    inference(subsumption_resolution,[],[f2112,f2265])).

fof(f2265,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_284 ),
    inference(unit_resulting_resolution,[],[f2177,f124])).

fof(f2177,plain,
    ( r2_hidden(sK10(k1_xboole_0),k1_xboole_0)
    | ~ spl14_284 ),
    inference(avatar_component_clause,[],[f2176])).

fof(f2176,plain,
    ( spl14_284
  <=> r2_hidden(sK10(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_284])])).

fof(f2309,plain,
    ( ~ spl14_282
    | ~ spl14_284 ),
    inference(avatar_contradiction_clause,[],[f2308])).

fof(f2308,plain,
    ( $false
    | ~ spl14_282
    | ~ spl14_284 ),
    inference(subsumption_resolution,[],[f2140,f2260])).

fof(f2260,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_284 ),
    inference(unit_resulting_resolution,[],[f2177,f2177,f115])).

fof(f2307,plain,
    ( ~ spl14_284
    | spl14_293 ),
    inference(avatar_contradiction_clause,[],[f2306])).

fof(f2306,plain,
    ( $false
    | ~ spl14_284
    | ~ spl14_293 ),
    inference(subsumption_resolution,[],[f2301,f2271])).

fof(f2271,plain,
    ( r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_284 ),
    inference(unit_resulting_resolution,[],[f112,f2177,f1729])).

fof(f2305,plain,
    ( spl14_292
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2246,f2108,f2303])).

fof(f2108,plain,
    ( spl14_279
  <=> ~ v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_279])])).

fof(f2246,plain,
    ( r2_hidden(sK11(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f112,f2109,f1723])).

fof(f2109,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl14_279 ),
    inference(avatar_component_clause,[],[f2108])).

fof(f2298,plain,
    ( ~ spl14_291
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2241,f2108,f2296])).

fof(f2241,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK10(k1_xboole_0)))
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f112,f2109,f770])).

fof(f2290,plain,
    ( ~ spl14_289
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2239,f2108,f2288])).

fof(f2239,plain,
    ( ~ r2_hidden(k1_xboole_0,sK10(k1_xboole_0))
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f112,f2109,f326])).

fof(f2236,plain,
    ( spl14_286
    | ~ spl14_278 ),
    inference(avatar_split_clause,[],[f2219,f2111,f2234])).

fof(f2219,plain,
    ( k1_xboole_0 = sK10(k1_zfmisc_1(k1_xboole_0))
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f112,f2183,f1730])).

fof(f2183,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK10(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f112,f2112,f127])).

fof(f2202,plain,
    ( ~ spl14_278
    | spl14_283 ),
    inference(avatar_contradiction_clause,[],[f2193])).

fof(f2193,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_283 ),
    inference(unit_resulting_resolution,[],[f2143,f2182,f114])).

fof(f2182,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl14_278 ),
    inference(unit_resulting_resolution,[],[f2112,f124])).

fof(f2143,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_283 ),
    inference(avatar_component_clause,[],[f2142])).

fof(f2142,plain,
    ( spl14_283
  <=> ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_283])])).

fof(f2201,plain,
    ( ~ spl14_278
    | spl14_283 ),
    inference(avatar_contradiction_clause,[],[f2191])).

fof(f2191,plain,
    ( $false
    | ~ spl14_278
    | ~ spl14_283 ),
    inference(unit_resulting_resolution,[],[f2143,f2182,f113])).

fof(f2178,plain,
    ( spl14_284
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2114,f2108,f2176])).

fof(f2114,plain,
    ( r2_hidden(sK10(k1_xboole_0),k1_xboole_0)
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f112,f2109,f119])).

fof(f2144,plain,
    ( ~ spl14_283
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2122,f2108,f2142])).

fof(f2122,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f112,f2109,f1715])).

fof(f2137,plain,
    ( ~ spl14_281
    | spl14_279 ),
    inference(avatar_split_clause,[],[f2117,f2108,f2135])).

fof(f2117,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl14_279 ),
    inference(unit_resulting_resolution,[],[f2109,f762])).

fof(f2113,plain,
    ( spl14_278
    | ~ spl14_248 ),
    inference(avatar_split_clause,[],[f2075,f1787,f2111])).

fof(f1787,plain,
    ( spl14_248
  <=> v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_248])])).

fof(f2075,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl14_248 ),
    inference(backward_demodulation,[],[f2058,f1788])).

fof(f1788,plain,
    ( v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl14_248 ),
    inference(avatar_component_clause,[],[f1787])).

fof(f2058,plain,
    ( u1_waybel_0(sK0,sK1) = k1_xboole_0
    | ~ spl14_248 ),
    inference(unit_resulting_resolution,[],[f1788,f98])).

fof(f2057,plain,
    ( spl14_276
    | spl14_265
    | ~ spl14_270 ),
    inference(avatar_split_clause,[],[f2013,f2010,f1960,f2055])).

fof(f2055,plain,
    ( spl14_276
  <=> r2_hidden(sK10(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_276])])).

fof(f1960,plain,
    ( spl14_265
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_265])])).

fof(f2010,plain,
    ( spl14_270
  <=> m1_subset_1(sK10(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_270])])).

fof(f2013,plain,
    ( r2_hidden(sK10(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_265
    | ~ spl14_270 ),
    inference(unit_resulting_resolution,[],[f1961,f2011,f119])).

fof(f2011,plain,
    ( m1_subset_1(sK10(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_270 ),
    inference(avatar_component_clause,[],[f2010])).

fof(f1961,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_265 ),
    inference(avatar_component_clause,[],[f1960])).

fof(f2038,plain,
    ( ~ spl14_275
    | spl14_249
    | spl14_265
    | ~ spl14_270 ),
    inference(avatar_split_clause,[],[f2020,f2010,f1960,f1784,f2036])).

fof(f2036,plain,
    ( spl14_275
  <=> ~ r1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_275])])).

fof(f1784,plain,
    ( spl14_249
  <=> ~ v1_xboole_0(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_249])])).

fof(f2020,plain,
    ( ~ r1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_249
    | ~ spl14_265
    | ~ spl14_270 ),
    inference(unit_resulting_resolution,[],[f1785,f112,f1961,f2011,f792])).

fof(f1785,plain,
    ( ~ v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ spl14_249 ),
    inference(avatar_component_clause,[],[f1784])).

fof(f2031,plain,
    ( ~ spl14_273
    | spl14_249
    | spl14_265
    | ~ spl14_270 ),
    inference(avatar_split_clause,[],[f2018,f2010,f1960,f1784,f2029])).

fof(f2029,plain,
    ( spl14_273
  <=> ~ r1_xboole_0(u1_waybel_0(sK0,sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_273])])).

fof(f2018,plain,
    ( ~ r1_xboole_0(u1_waybel_0(sK0,sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_249
    | ~ spl14_265
    | ~ spl14_270 ),
    inference(unit_resulting_resolution,[],[f1785,f112,f1961,f2011,f792])).

fof(f2012,plain,
    ( spl14_270
    | ~ spl14_134
    | ~ spl14_258 ),
    inference(avatar_split_clause,[],[f1949,f1851,f724,f2010])).

fof(f724,plain,
    ( spl14_134
  <=> m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_134])])).

fof(f1949,plain,
    ( m1_subset_1(sK10(u1_waybel_0(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_134
    | ~ spl14_258 ),
    inference(unit_resulting_resolution,[],[f1852,f725,f126])).

fof(f725,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_134 ),
    inference(avatar_component_clause,[],[f724])).

fof(f2004,plain,
    ( ~ spl14_269
    | spl14_267 ),
    inference(avatar_split_clause,[],[f1995,f1991,f2002])).

fof(f2002,plain,
    ( spl14_269
  <=> ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK10(u1_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_269])])).

fof(f1991,plain,
    ( spl14_267
  <=> ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK10(u1_waybel_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_267])])).

fof(f1995,plain,
    ( ~ r2_hidden(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK10(u1_waybel_0(sK0,sK1))))
    | ~ spl14_267 ),
    inference(unit_resulting_resolution,[],[f1992,f118])).

fof(f1992,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK10(u1_waybel_0(sK0,sK1))))
    | ~ spl14_267 ),
    inference(avatar_component_clause,[],[f1991])).

fof(f1993,plain,
    ( ~ spl14_267
    | spl14_249 ),
    inference(avatar_split_clause,[],[f1895,f1784,f1991])).

fof(f1895,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(sK10(u1_waybel_0(sK0,sK1))))
    | ~ spl14_249 ),
    inference(unit_resulting_resolution,[],[f112,f1785,f770])).

fof(f1962,plain,
    ( ~ spl14_265
    | ~ spl14_134
    | ~ spl14_258 ),
    inference(avatar_split_clause,[],[f1950,f1851,f724,f1960])).

fof(f1950,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ spl14_134
    | ~ spl14_258 ),
    inference(unit_resulting_resolution,[],[f1852,f725,f127])).

fof(f1948,plain,
    ( ~ spl14_263
    | spl14_249 ),
    inference(avatar_split_clause,[],[f1893,f1784,f1946])).

fof(f1946,plain,
    ( spl14_263
  <=> ~ r2_hidden(u1_waybel_0(sK0,sK1),sK10(u1_waybel_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_263])])).

fof(f1893,plain,
    ( ~ r2_hidden(u1_waybel_0(sK0,sK1),sK10(u1_waybel_0(sK0,sK1)))
    | ~ spl14_249 ),
    inference(unit_resulting_resolution,[],[f112,f1785,f326])).

fof(f1890,plain,
    ( spl14_260
    | ~ spl14_60
    | ~ spl14_248 ),
    inference(avatar_split_clause,[],[f1865,f1787,f378,f1888])).

fof(f1888,plain,
    ( spl14_260
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_260])])).

fof(f378,plain,
    ( spl14_60
  <=> v1_funct_1(u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_60])])).

fof(f1865,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl14_60
    | ~ spl14_248 ),
    inference(backward_demodulation,[],[f1854,f379])).

fof(f379,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl14_60 ),
    inference(avatar_component_clause,[],[f378])).

fof(f1854,plain,
    ( u1_waybel_0(sK0,sK1) = k1_xboole_0
    | ~ spl14_248 ),
    inference(unit_resulting_resolution,[],[f1788,f98])).

fof(f1853,plain,
    ( spl14_258
    | spl14_249 ),
    inference(avatar_split_clause,[],[f1797,f1784,f1851])).

fof(f1797,plain,
    ( r2_hidden(sK10(u1_waybel_0(sK0,sK1)),u1_waybel_0(sK0,sK1))
    | ~ spl14_249 ),
    inference(unit_resulting_resolution,[],[f112,f1785,f119])).

fof(f1846,plain,
    ( spl14_256
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f651,f572,f251,f157,f150,f1844])).

fof(f1844,plain,
    ( spl14_256
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_256])])).

fof(f651,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f112,f103])).

fof(f1829,plain,
    ( ~ spl14_255
    | spl14_249 ),
    inference(avatar_split_clause,[],[f1807,f1784,f1827])).

fof(f1827,plain,
    ( spl14_255
  <=> ~ r1_xboole_0(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_255])])).

fof(f1807,plain,
    ( ~ r1_xboole_0(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1))
    | ~ spl14_249 ),
    inference(unit_resulting_resolution,[],[f112,f1785,f1715])).

fof(f1822,plain,
    ( ~ spl14_253
    | spl14_249 ),
    inference(avatar_split_clause,[],[f1801,f1784,f1820])).

fof(f1820,plain,
    ( spl14_253
  <=> ~ m1_subset_1(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_253])])).

fof(f1801,plain,
    ( ~ m1_subset_1(u1_waybel_0(sK0,sK1),u1_waybel_0(sK0,sK1))
    | ~ spl14_249 ),
    inference(unit_resulting_resolution,[],[f1785,f762])).

fof(f1796,plain,
    ( spl14_250
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f650,f564,f251,f157,f150,f1794])).

fof(f1794,plain,
    ( spl14_250
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_250])])).

fof(f650,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f112,f103])).

fof(f1789,plain,
    ( ~ spl14_247
    | spl14_248
    | spl14_145 ),
    inference(avatar_split_clause,[],[f782,f779,f1787,f1781])).

fof(f1781,plain,
    ( spl14_247
  <=> ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_247])])).

fof(f779,plain,
    ( spl14_145
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_145])])).

fof(f782,plain,
    ( v1_xboole_0(u1_waybel_0(sK0,sK1))
    | ~ m1_subset_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_145 ),
    inference(resolution,[],[f780,f119])).

fof(f780,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_145 ),
    inference(avatar_component_clause,[],[f779])).

fof(f1760,plain,
    ( spl14_244
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f626,f572,f251,f157,f150,f1758])).

fof(f1758,plain,
    ( spl14_244
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_244])])).

fof(f626,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f573,f102])).

fof(f1722,plain,
    ( spl14_242
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f623,f564,f251,f157,f150,f1720])).

fof(f1720,plain,
    ( spl14_242
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_242])])).

fof(f623,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f565,f102])).

fof(f1707,plain,
    ( spl14_240
    | ~ spl14_238 ),
    inference(avatar_split_clause,[],[f1700,f1623,f1705])).

fof(f1705,plain,
    ( spl14_240
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_240])])).

fof(f1623,plain,
    ( spl14_238
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_238])])).

fof(f1700,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK1))))))
    | ~ spl14_238 ),
    inference(unit_resulting_resolution,[],[f1624,f97])).

fof(f97,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',dt_l1_orders_2)).

fof(f1624,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK1))))))
    | ~ spl14_238 ),
    inference(avatar_component_clause,[],[f1623])).

fof(f1625,plain,
    ( spl14_238
    | ~ spl14_174
    | ~ spl14_236 ),
    inference(avatar_split_clause,[],[f1615,f1612,f962,f1623])).

fof(f962,plain,
    ( spl14_174
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_174])])).

fof(f1612,plain,
    ( spl14_236
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK1))))),sK4(sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_236])])).

fof(f1615,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK1))))))
    | ~ spl14_174
    | ~ spl14_236 ),
    inference(unit_resulting_resolution,[],[f963,f1613,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( l1_orders_2(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',dt_l1_waybel_0)).

fof(f1613,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK1))))),sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_236 ),
    inference(avatar_component_clause,[],[f1612])).

fof(f963,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_174 ),
    inference(avatar_component_clause,[],[f962])).

fof(f1614,plain,
    ( spl14_236
    | ~ spl14_174 ),
    inference(avatar_split_clause,[],[f965,f962,f1612])).

fof(f965,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK1))))),sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_174 ),
    inference(unit_resulting_resolution,[],[f963,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_waybel_0(sK4(X0),X0)
      | ~ l1_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f40,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
     => l1_waybel_0(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ? [X1] : l1_waybel_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',existence_l1_waybel_0)).

fof(f1606,plain,
    ( spl14_234
    | ~ spl14_232 ),
    inference(avatar_split_clause,[],[f1531,f1528,f1604])).

fof(f1604,plain,
    ( spl14_234
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_234])])).

fof(f1528,plain,
    ( spl14_232
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_232])])).

fof(f1531,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK12))))))
    | ~ spl14_232 ),
    inference(unit_resulting_resolution,[],[f1529,f97])).

fof(f1529,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK12))))))
    | ~ spl14_232 ),
    inference(avatar_component_clause,[],[f1528])).

fof(f1530,plain,
    ( spl14_232
    | ~ spl14_168
    | ~ spl14_230 ),
    inference(avatar_split_clause,[],[f1520,f1517,f910,f1528])).

fof(f910,plain,
    ( spl14_168
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_168])])).

fof(f1517,plain,
    ( spl14_230
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK12))))),sK4(sK4(sK4(sK4(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_230])])).

fof(f1520,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK12))))))
    | ~ spl14_168
    | ~ spl14_230 ),
    inference(unit_resulting_resolution,[],[f911,f1518,f99])).

fof(f1518,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK12))))),sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_230 ),
    inference(avatar_component_clause,[],[f1517])).

fof(f911,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_168 ),
    inference(avatar_component_clause,[],[f910])).

fof(f1519,plain,
    ( spl14_230
    | ~ spl14_168 ),
    inference(avatar_split_clause,[],[f913,f910,f1517])).

fof(f913,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK12))))),sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_168 ),
    inference(unit_resulting_resolution,[],[f911,f100])).

fof(f1449,plain,
    ( spl14_228
    | ~ spl14_226 ),
    inference(avatar_split_clause,[],[f1442,f1439,f1447])).

fof(f1447,plain,
    ( spl14_228
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_228])])).

fof(f1439,plain,
    ( spl14_226
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_226])])).

fof(f1442,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK13))))))
    | ~ spl14_226 ),
    inference(unit_resulting_resolution,[],[f1440,f97])).

fof(f1440,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK13))))))
    | ~ spl14_226 ),
    inference(avatar_component_clause,[],[f1439])).

fof(f1441,plain,
    ( spl14_226
    | ~ spl14_160
    | ~ spl14_224 ),
    inference(avatar_split_clause,[],[f1431,f1428,f876,f1439])).

fof(f876,plain,
    ( spl14_160
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_160])])).

fof(f1428,plain,
    ( spl14_224
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK13))))),sK4(sK4(sK4(sK4(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_224])])).

fof(f1431,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK13))))))
    | ~ spl14_160
    | ~ spl14_224 ),
    inference(unit_resulting_resolution,[],[f877,f1429,f99])).

fof(f1429,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK13))))),sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_224 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f877,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_160 ),
    inference(avatar_component_clause,[],[f876])).

fof(f1430,plain,
    ( spl14_224
    | ~ spl14_160 ),
    inference(avatar_split_clause,[],[f879,f876,f1428])).

fof(f879,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK13))))),sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_160 ),
    inference(unit_resulting_resolution,[],[f877,f100])).

fof(f1366,plain,
    ( spl14_222
    | ~ spl14_220 ),
    inference(avatar_split_clause,[],[f1359,f1356,f1364])).

fof(f1364,plain,
    ( spl14_222
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_222])])).

fof(f1356,plain,
    ( spl14_220
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_220])])).

fof(f1359,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK4(sK0))))))
    | ~ spl14_220 ),
    inference(unit_resulting_resolution,[],[f1357,f97])).

fof(f1357,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK0))))))
    | ~ spl14_220 ),
    inference(avatar_component_clause,[],[f1356])).

fof(f1358,plain,
    ( spl14_220
    | ~ spl14_154
    | ~ spl14_216 ),
    inference(avatar_split_clause,[],[f1348,f1338,f846,f1356])).

fof(f846,plain,
    ( spl14_154
  <=> l1_struct_0(sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_154])])).

fof(f1338,plain,
    ( spl14_216
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK0))))),sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_216])])).

fof(f1348,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK4(sK0))))))
    | ~ spl14_154
    | ~ spl14_216 ),
    inference(unit_resulting_resolution,[],[f847,f1339,f99])).

fof(f1339,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK0))))),sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_216 ),
    inference(avatar_component_clause,[],[f1338])).

fof(f847,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_154 ),
    inference(avatar_component_clause,[],[f846])).

fof(f1347,plain,
    ( spl14_218
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f620,f251,f157,f150,f1345])).

fof(f1345,plain,
    ( spl14_218
  <=> r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_218])])).

fof(f620,plain,
    ( r1_orders_2(sK1,sK10(u1_struct_0(sK1)),sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1))))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f112,f102])).

fof(f1340,plain,
    ( spl14_216
    | ~ spl14_154 ),
    inference(avatar_split_clause,[],[f852,f846,f1338])).

fof(f852,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK4(sK0))))),sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_154 ),
    inference(unit_resulting_resolution,[],[f847,f100])).

fof(f1321,plain,
    ( spl14_214
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f596,f572,f251,f157,f150,f1319])).

fof(f596,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f573,f101])).

fof(f101,plain,(
    ! [X4,X0,X5] :
      ( m1_subset_1(sK7(X0,X4,X5),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v7_waybel_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f1280,plain,
    ( spl14_212
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f595,f572,f564,f251,f157,f150,f1278])).

fof(f595,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f573,f101])).

fof(f1272,plain,
    ( ~ spl14_211
    | ~ spl14_208 ),
    inference(avatar_split_clause,[],[f1264,f1261,f1270])).

fof(f1270,plain,
    ( spl14_211
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)),u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_211])])).

fof(f1261,plain,
    ( spl14_208
  <=> m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_208])])).

fof(f1264,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1)),u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl14_208 ),
    inference(unit_resulting_resolution,[],[f1262,f765])).

fof(f1262,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl14_208 ),
    inference(avatar_component_clause,[],[f1261])).

fof(f1263,plain,
    ( spl14_208
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f502,f315,f259,f1261])).

fof(f259,plain,
    ( spl14_32
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f315,plain,
    ( spl14_46
  <=> l1_waybel_0(sK4(sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_46])])).

fof(f502,plain,
    ( m1_subset_1(u1_waybel_0(sK1,sK4(sK1)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK1)),u1_struct_0(sK1))))
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f260,f316,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) )
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l1_waybel_0(X1,X0)
        & l1_struct_0(X0) )
     => ( m1_subset_1(u1_waybel_0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        & v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
        & v1_funct_1(u1_waybel_0(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',dt_u1_waybel_0)).

fof(f316,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl14_46 ),
    inference(avatar_component_clause,[],[f315])).

fof(f260,plain,
    ( l1_struct_0(sK1)
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f259])).

fof(f1255,plain,
    ( spl14_206
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f593,f572,f564,f251,f157,f150,f1253])).

fof(f593,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f565,f101])).

fof(f1248,plain,
    ( ~ spl14_205
    | ~ spl14_202 ),
    inference(avatar_split_clause,[],[f1240,f1237,f1246])).

fof(f1246,plain,
    ( spl14_205
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK12)),u1_struct_0(sK12)),u1_waybel_0(sK12,sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_205])])).

fof(f1237,plain,
    ( spl14_202
  <=> m1_subset_1(u1_waybel_0(sK12,sK4(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK12)),u1_struct_0(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_202])])).

fof(f1240,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK12)),u1_struct_0(sK12)),u1_waybel_0(sK12,sK4(sK12)))
    | ~ spl14_202 ),
    inference(unit_resulting_resolution,[],[f1238,f765])).

fof(f1238,plain,
    ( m1_subset_1(u1_waybel_0(sK12,sK4(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK12)),u1_struct_0(sK12))))
    | ~ spl14_202 ),
    inference(avatar_component_clause,[],[f1237])).

fof(f1239,plain,
    ( spl14_202
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f507,f240,f207,f1237])).

fof(f207,plain,
    ( spl14_20
  <=> l1_struct_0(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_20])])).

fof(f240,plain,
    ( spl14_28
  <=> l1_waybel_0(sK4(sK12),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_28])])).

fof(f507,plain,
    ( m1_subset_1(u1_waybel_0(sK12,sK4(sK12)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK12)),u1_struct_0(sK12))))
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f208,f241,f122])).

fof(f241,plain,
    ( l1_waybel_0(sK4(sK12),sK12)
    | ~ spl14_28 ),
    inference(avatar_component_clause,[],[f240])).

fof(f208,plain,
    ( l1_struct_0(sK12)
    | ~ spl14_20 ),
    inference(avatar_component_clause,[],[f207])).

fof(f1231,plain,
    ( ~ spl14_201
    | ~ spl14_196 ),
    inference(avatar_split_clause,[],[f1216,f1213,f1229])).

fof(f1229,plain,
    ( spl14_201
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK13)),u1_struct_0(sK13)),u1_waybel_0(sK13,sK4(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_201])])).

fof(f1213,plain,
    ( spl14_196
  <=> m1_subset_1(u1_waybel_0(sK13,sK4(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK13)),u1_struct_0(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_196])])).

fof(f1216,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK13)),u1_struct_0(sK13)),u1_waybel_0(sK13,sK4(sK13)))
    | ~ spl14_196 ),
    inference(unit_resulting_resolution,[],[f1214,f765])).

fof(f1214,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK4(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK13)),u1_struct_0(sK13))))
    | ~ spl14_196 ),
    inference(avatar_component_clause,[],[f1213])).

fof(f1224,plain,
    ( spl14_198
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f592,f564,f251,f157,f150,f1222])).

fof(f592,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f565,f101])).

fof(f1215,plain,
    ( spl14_196
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f508,f224,f171,f1213])).

fof(f171,plain,
    ( spl14_10
  <=> l1_struct_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f224,plain,
    ( spl14_24
  <=> l1_waybel_0(sK4(sK13),sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_24])])).

fof(f508,plain,
    ( m1_subset_1(u1_waybel_0(sK13,sK4(sK13)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK13)),u1_struct_0(sK13))))
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f172,f225,f122])).

fof(f225,plain,
    ( l1_waybel_0(sK4(sK13),sK13)
    | ~ spl14_24 ),
    inference(avatar_component_clause,[],[f224])).

fof(f172,plain,
    ( l1_struct_0(sK13)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f1047,plain,
    ( ~ spl14_195
    | ~ spl14_176 ),
    inference(avatar_split_clause,[],[f1039,f972,f1045])).

fof(f1045,plain,
    ( spl14_195
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),u1_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_195])])).

fof(f972,plain,
    ( spl14_176
  <=> m1_subset_1(u1_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_176])])).

fof(f1039,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0)),u1_waybel_0(sK0,sK4(sK0)))
    | ~ spl14_176 ),
    inference(unit_resulting_resolution,[],[f973,f765])).

fof(f973,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl14_176 ),
    inference(avatar_component_clause,[],[f972])).

fof(f1038,plain,
    ( spl14_192
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f594,f572,f251,f157,f150,f1036])).

fof(f594,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK3)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f573,f101])).

fof(f1031,plain,
    ( spl14_190
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f591,f564,f251,f157,f150,f1029])).

fof(f591,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f565,f101])).

fof(f1024,plain,
    ( spl14_188
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f590,f572,f251,f157,f150,f1022])).

fof(f590,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK3),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f573,f112,f101])).

fof(f1017,plain,
    ( spl14_186
    | ~ spl14_122
    | ~ spl14_170 ),
    inference(avatar_split_clause,[],[f922,f918,f681,f1015])).

fof(f1015,plain,
    ( spl14_186
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK1))),sK4(sK4(sK4(sK4(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_186])])).

fof(f681,plain,
    ( spl14_122
  <=> l1_struct_0(sK4(sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_122])])).

fof(f918,plain,
    ( spl14_170
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK1)))),sK4(sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_170])])).

fof(f922,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK1))),sK4(sK4(sK4(sK4(sK1))))))
    | ~ spl14_122
    | ~ spl14_170 ),
    inference(unit_resulting_resolution,[],[f682,f919,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( v1_funct_1(u1_waybel_0(X0,X1))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f919,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK1)))),sK4(sK4(sK4(sK1))))
    | ~ spl14_170 ),
    inference(avatar_component_clause,[],[f918])).

fof(f682,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK1))))
    | ~ spl14_122 ),
    inference(avatar_component_clause,[],[f681])).

fof(f1010,plain,
    ( spl14_184
    | ~ spl14_116
    | ~ spl14_162 ),
    inference(avatar_split_clause,[],[f888,f884,f645,f1008])).

fof(f1008,plain,
    ( spl14_184
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK12))),sK4(sK4(sK4(sK4(sK12)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_184])])).

fof(f645,plain,
    ( spl14_116
  <=> l1_struct_0(sK4(sK4(sK4(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_116])])).

fof(f884,plain,
    ( spl14_162
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK12)))),sK4(sK4(sK4(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_162])])).

fof(f888,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK12))),sK4(sK4(sK4(sK4(sK12))))))
    | ~ spl14_116
    | ~ spl14_162 ),
    inference(unit_resulting_resolution,[],[f646,f885,f120])).

fof(f885,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK12)))),sK4(sK4(sK4(sK12))))
    | ~ spl14_162 ),
    inference(avatar_component_clause,[],[f884])).

fof(f646,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK12))))
    | ~ spl14_116 ),
    inference(avatar_component_clause,[],[f645])).

fof(f1003,plain,
    ( spl14_182
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f589,f564,f251,f157,f150,f1001])).

fof(f589,plain,
    ( m1_subset_1(sK7(sK1,sK9(sK0,sK1,sK2),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f565,f112,f101])).

fof(f996,plain,
    ( spl14_180
    | ~ spl14_110
    | ~ spl14_156 ),
    inference(avatar_split_clause,[],[f861,f857,f609,f994])).

fof(f994,plain,
    ( spl14_180
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK13))),sK4(sK4(sK4(sK4(sK13)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_180])])).

fof(f609,plain,
    ( spl14_110
  <=> l1_struct_0(sK4(sK4(sK4(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_110])])).

fof(f857,plain,
    ( spl14_156
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK13)))),sK4(sK4(sK4(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_156])])).

fof(f861,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK13))),sK4(sK4(sK4(sK4(sK13))))))
    | ~ spl14_110
    | ~ spl14_156 ),
    inference(unit_resulting_resolution,[],[f610,f858,f120])).

fof(f858,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK13)))),sK4(sK4(sK4(sK13))))
    | ~ spl14_156 ),
    inference(avatar_component_clause,[],[f857])).

fof(f610,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK13))))
    | ~ spl14_110 ),
    inference(avatar_component_clause,[],[f609])).

fof(f989,plain,
    ( spl14_178
    | ~ spl14_100
    | ~ spl14_150 ),
    inference(avatar_split_clause,[],[f831,f827,f556,f987])).

fof(f987,plain,
    ( spl14_178
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK0))),sK4(sK4(sK4(sK4(sK0)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_178])])).

fof(f556,plain,
    ( spl14_100
  <=> l1_struct_0(sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_100])])).

fof(f827,plain,
    ( spl14_150
  <=> l1_waybel_0(sK4(sK4(sK4(sK4(sK0)))),sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_150])])).

fof(f831,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK4(sK0))),sK4(sK4(sK4(sK4(sK0))))))
    | ~ spl14_100
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f557,f828,f120])).

fof(f828,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK0)))),sK4(sK4(sK4(sK0))))
    | ~ spl14_150 ),
    inference(avatar_component_clause,[],[f827])).

fof(f557,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK0))))
    | ~ spl14_100 ),
    inference(avatar_component_clause,[],[f556])).

fof(f974,plain,
    ( spl14_176
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f501,f217,f143,f972])).

fof(f217,plain,
    ( spl14_22
  <=> l1_waybel_0(sK4(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_22])])).

fof(f501,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK4(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4(sK0)),u1_struct_0(sK0))))
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f144,f218,f122])).

fof(f218,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl14_22 ),
    inference(avatar_component_clause,[],[f217])).

fof(f964,plain,
    ( spl14_174
    | ~ spl14_172 ),
    inference(avatar_split_clause,[],[f957,f954,f962])).

fof(f954,plain,
    ( spl14_172
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_172])])).

fof(f957,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_172 ),
    inference(unit_resulting_resolution,[],[f955,f97])).

fof(f955,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_172 ),
    inference(avatar_component_clause,[],[f954])).

fof(f956,plain,
    ( spl14_172
    | ~ spl14_122
    | ~ spl14_170 ),
    inference(avatar_split_clause,[],[f921,f918,f681,f954])).

fof(f921,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK1)))))
    | ~ spl14_122
    | ~ spl14_170 ),
    inference(unit_resulting_resolution,[],[f682,f919,f99])).

fof(f920,plain,
    ( spl14_170
    | ~ spl14_122 ),
    inference(avatar_split_clause,[],[f684,f681,f918])).

fof(f684,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK1)))),sK4(sK4(sK4(sK1))))
    | ~ spl14_122 ),
    inference(unit_resulting_resolution,[],[f682,f100])).

fof(f912,plain,
    ( spl14_168
    | ~ spl14_164 ),
    inference(avatar_split_clause,[],[f905,f895,f910])).

fof(f895,plain,
    ( spl14_164
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_164])])).

fof(f905,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_164 ),
    inference(unit_resulting_resolution,[],[f896,f97])).

fof(f896,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_164 ),
    inference(avatar_component_clause,[],[f895])).

fof(f904,plain,
    ( spl14_166
    | spl14_5
    | ~ spl14_6
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f588,f251,f157,f150,f902])).

fof(f588,plain,
    ( m1_subset_1(sK7(sK1,sK10(u1_struct_0(sK1)),sK10(u1_struct_0(sK1))),u1_struct_0(sK1))
    | ~ spl14_5
    | ~ spl14_6
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f151,f252,f158,f112,f112,f101])).

fof(f897,plain,
    ( spl14_164
    | ~ spl14_116
    | ~ spl14_162 ),
    inference(avatar_split_clause,[],[f887,f884,f645,f895])).

fof(f887,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK12)))))
    | ~ spl14_116
    | ~ spl14_162 ),
    inference(unit_resulting_resolution,[],[f646,f885,f99])).

fof(f886,plain,
    ( spl14_162
    | ~ spl14_116 ),
    inference(avatar_split_clause,[],[f648,f645,f884])).

fof(f648,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK12)))),sK4(sK4(sK4(sK12))))
    | ~ spl14_116 ),
    inference(unit_resulting_resolution,[],[f646,f100])).

fof(f878,plain,
    ( spl14_160
    | ~ spl14_158 ),
    inference(avatar_split_clause,[],[f871,f868,f876])).

fof(f868,plain,
    ( spl14_158
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_158])])).

fof(f871,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_158 ),
    inference(unit_resulting_resolution,[],[f869,f97])).

fof(f869,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_158 ),
    inference(avatar_component_clause,[],[f868])).

fof(f870,plain,
    ( spl14_158
    | ~ spl14_110
    | ~ spl14_156 ),
    inference(avatar_split_clause,[],[f860,f857,f609,f868])).

fof(f860,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK13)))))
    | ~ spl14_110
    | ~ spl14_156 ),
    inference(unit_resulting_resolution,[],[f610,f858,f99])).

fof(f859,plain,
    ( spl14_156
    | ~ spl14_110 ),
    inference(avatar_split_clause,[],[f612,f609,f857])).

fof(f612,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK13)))),sK4(sK4(sK4(sK13))))
    | ~ spl14_110 ),
    inference(unit_resulting_resolution,[],[f610,f100])).

fof(f848,plain,
    ( spl14_154
    | ~ spl14_152 ),
    inference(avatar_split_clause,[],[f841,f838,f846])).

fof(f838,plain,
    ( spl14_152
  <=> l1_orders_2(sK4(sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_152])])).

fof(f841,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_152 ),
    inference(unit_resulting_resolution,[],[f839,f97])).

fof(f839,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_152 ),
    inference(avatar_component_clause,[],[f838])).

fof(f840,plain,
    ( spl14_152
    | ~ spl14_100
    | ~ spl14_150 ),
    inference(avatar_split_clause,[],[f830,f827,f556,f838])).

fof(f830,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK4(sK0)))))
    | ~ spl14_100
    | ~ spl14_150 ),
    inference(unit_resulting_resolution,[],[f557,f828,f99])).

fof(f829,plain,
    ( spl14_150
    | ~ spl14_100 ),
    inference(avatar_split_clause,[],[f559,f556,f827])).

fof(f559,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK4(sK0)))),sK4(sK4(sK4(sK0))))
    | ~ spl14_100 ),
    inference(unit_resulting_resolution,[],[f557,f100])).

fof(f807,plain,
    ( spl14_148
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f471,f315,f259,f805])).

fof(f805,plain,
    ( spl14_148
  <=> v1_funct_2(u1_waybel_0(sK1,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_148])])).

fof(f471,plain,
    ( v1_funct_2(u1_waybel_0(sK1,sK4(sK1)),u1_struct_0(sK4(sK1)),u1_struct_0(sK1))
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f260,f316,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( v1_funct_2(u1_waybel_0(X0,X1),u1_struct_0(X1),u1_struct_0(X0))
      | ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f800,plain,
    ( spl14_146
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f476,f240,f207,f798])).

fof(f798,plain,
    ( spl14_146
  <=> v1_funct_2(u1_waybel_0(sK12,sK4(sK12)),u1_struct_0(sK4(sK12)),u1_struct_0(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_146])])).

fof(f476,plain,
    ( v1_funct_2(u1_waybel_0(sK12,sK4(sK12)),u1_struct_0(sK4(sK12)),u1_struct_0(sK12))
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f208,f241,f121])).

fof(f781,plain,
    ( ~ spl14_145
    | ~ spl14_134 ),
    inference(avatar_split_clause,[],[f768,f724,f779])).

fof(f768,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)),u1_waybel_0(sK0,sK1))
    | ~ spl14_134 ),
    inference(unit_resulting_resolution,[],[f725,f765])).

fof(f756,plain,
    ( spl14_142
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f477,f224,f171,f754])).

fof(f754,plain,
    ( spl14_142
  <=> v1_funct_2(u1_waybel_0(sK13,sK4(sK13)),u1_struct_0(sK4(sK13)),u1_struct_0(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_142])])).

fof(f477,plain,
    ( v1_funct_2(u1_waybel_0(sK13,sK4(sK13)),u1_struct_0(sK4(sK13)),u1_struct_0(sK13))
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f172,f225,f121])).

fof(f749,plain,
    ( spl14_140
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_104 ),
    inference(avatar_split_clause,[],[f576,f572,f178,f150,f143,f136,f747])).

fof(f747,plain,
    ( spl14_140
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_140])])).

fof(f576,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_104 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f573,f125])).

fof(f740,plain,
    ( spl14_138
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_102 ),
    inference(avatar_split_clause,[],[f575,f564,f178,f150,f143,f136,f738])).

fof(f738,plain,
    ( spl14_138
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_138])])).

fof(f575,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK9(sK0,sK1,sK2)),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_102 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f565,f125])).

fof(f733,plain,
    ( spl14_136
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f470,f217,f143,f731])).

fof(f731,plain,
    ( spl14_136
  <=> v1_funct_2(u1_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_136])])).

fof(f470,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK4(sK0)),u1_struct_0(sK4(sK0)),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f144,f218,f121])).

fof(f726,plain,
    ( spl14_134
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f500,f178,f143,f724])).

fof(f500,plain,
    ( m1_subset_1(u1_waybel_0(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f144,f179,f122])).

fof(f719,plain,
    ( spl14_132
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(avatar_split_clause,[],[f667,f662,f482,f717])).

fof(f717,plain,
    ( spl14_132
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK1)),sK4(sK4(sK4(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_132])])).

fof(f482,plain,
    ( spl14_84
  <=> l1_struct_0(sK4(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f662,plain,
    ( spl14_118
  <=> l1_waybel_0(sK4(sK4(sK4(sK1))),sK4(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_118])])).

fof(f667,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK1)),sK4(sK4(sK4(sK1)))))
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(unit_resulting_resolution,[],[f483,f663,f120])).

fof(f663,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK1))),sK4(sK4(sK1)))
    | ~ spl14_118 ),
    inference(avatar_component_clause,[],[f662])).

fof(f483,plain,
    ( l1_struct_0(sK4(sK4(sK1)))
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f482])).

fof(f712,plain,
    ( spl14_130
    | ~ spl14_78
    | ~ spl14_112 ),
    inference(avatar_split_clause,[],[f631,f617,f448,f710])).

fof(f710,plain,
    ( spl14_130
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK12)),sK4(sK4(sK4(sK12))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_130])])).

fof(f448,plain,
    ( spl14_78
  <=> l1_struct_0(sK4(sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_78])])).

fof(f617,plain,
    ( spl14_112
  <=> l1_waybel_0(sK4(sK4(sK4(sK12))),sK4(sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_112])])).

fof(f631,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK12)),sK4(sK4(sK4(sK12)))))
    | ~ spl14_78
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f449,f618,f120])).

fof(f618,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK12))),sK4(sK4(sK12)))
    | ~ spl14_112 ),
    inference(avatar_component_clause,[],[f617])).

fof(f449,plain,
    ( l1_struct_0(sK4(sK4(sK12)))
    | ~ spl14_78 ),
    inference(avatar_component_clause,[],[f448])).

fof(f705,plain,
    ( spl14_128
    | ~ spl14_72
    | ~ spl14_106 ),
    inference(avatar_split_clause,[],[f586,f581,f423,f703])).

fof(f703,plain,
    ( spl14_128
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK13)),sK4(sK4(sK4(sK13))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_128])])).

fof(f423,plain,
    ( spl14_72
  <=> l1_struct_0(sK4(sK4(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_72])])).

fof(f581,plain,
    ( spl14_106
  <=> l1_waybel_0(sK4(sK4(sK4(sK13))),sK4(sK4(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_106])])).

fof(f586,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK13)),sK4(sK4(sK4(sK13)))))
    | ~ spl14_72
    | ~ spl14_106 ),
    inference(unit_resulting_resolution,[],[f424,f582,f120])).

fof(f582,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK13))),sK4(sK4(sK13)))
    | ~ spl14_106 ),
    inference(avatar_component_clause,[],[f581])).

fof(f424,plain,
    ( l1_struct_0(sK4(sK4(sK13)))
    | ~ spl14_72 ),
    inference(avatar_component_clause,[],[f423])).

fof(f698,plain,
    ( spl14_126
    | ~ spl14_56
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f540,f535,f357,f696])).

fof(f696,plain,
    ( spl14_126
  <=> v1_funct_1(u1_waybel_0(sK4(sK4(sK0)),sK4(sK4(sK4(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_126])])).

fof(f357,plain,
    ( spl14_56
  <=> l1_struct_0(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_56])])).

fof(f535,plain,
    ( spl14_96
  <=> l1_waybel_0(sK4(sK4(sK4(sK0))),sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_96])])).

fof(f540,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK4(sK0)),sK4(sK4(sK4(sK0)))))
    | ~ spl14_56
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f358,f536,f120])).

fof(f536,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK0))),sK4(sK4(sK0)))
    | ~ spl14_96 ),
    inference(avatar_component_clause,[],[f535])).

fof(f358,plain,
    ( l1_struct_0(sK4(sK4(sK0)))
    | ~ spl14_56 ),
    inference(avatar_component_clause,[],[f357])).

fof(f691,plain,
    ( spl14_124
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f567,f178,f150,f143,f136,f689])).

fof(f689,plain,
    ( spl14_124
  <=> m1_subset_1(k2_waybel_0(sK0,sK1,sK10(u1_struct_0(sK1))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_124])])).

fof(f567,plain,
    ( m1_subset_1(k2_waybel_0(sK0,sK1,sK10(u1_struct_0(sK1))),u1_struct_0(sK0))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f112,f125])).

fof(f683,plain,
    ( spl14_122
    | ~ spl14_120 ),
    inference(avatar_split_clause,[],[f676,f673,f681])).

fof(f673,plain,
    ( spl14_120
  <=> l1_orders_2(sK4(sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_120])])).

fof(f676,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK1))))
    | ~ spl14_120 ),
    inference(unit_resulting_resolution,[],[f674,f97])).

fof(f674,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK1))))
    | ~ spl14_120 ),
    inference(avatar_component_clause,[],[f673])).

fof(f675,plain,
    ( spl14_120
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(avatar_split_clause,[],[f668,f662,f482,f673])).

fof(f668,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK1))))
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(unit_resulting_resolution,[],[f483,f663,f99])).

fof(f664,plain,
    ( spl14_118
    | ~ spl14_84 ),
    inference(avatar_split_clause,[],[f485,f482,f662])).

fof(f485,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK1))),sK4(sK4(sK1)))
    | ~ spl14_84 ),
    inference(unit_resulting_resolution,[],[f483,f100])).

fof(f647,plain,
    ( spl14_116
    | ~ spl14_114 ),
    inference(avatar_split_clause,[],[f640,f637,f645])).

fof(f637,plain,
    ( spl14_114
  <=> l1_orders_2(sK4(sK4(sK4(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_114])])).

fof(f640,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK12))))
    | ~ spl14_114 ),
    inference(unit_resulting_resolution,[],[f638,f97])).

fof(f638,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK12))))
    | ~ spl14_114 ),
    inference(avatar_component_clause,[],[f637])).

fof(f639,plain,
    ( spl14_114
    | ~ spl14_78
    | ~ spl14_112 ),
    inference(avatar_split_clause,[],[f632,f617,f448,f637])).

fof(f632,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK12))))
    | ~ spl14_78
    | ~ spl14_112 ),
    inference(unit_resulting_resolution,[],[f449,f618,f99])).

fof(f619,plain,
    ( spl14_112
    | ~ spl14_78 ),
    inference(avatar_split_clause,[],[f451,f448,f617])).

fof(f451,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK12))),sK4(sK4(sK12)))
    | ~ spl14_78 ),
    inference(unit_resulting_resolution,[],[f449,f100])).

fof(f611,plain,
    ( spl14_110
    | ~ spl14_108 ),
    inference(avatar_split_clause,[],[f604,f601,f609])).

fof(f601,plain,
    ( spl14_108
  <=> l1_orders_2(sK4(sK4(sK4(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_108])])).

fof(f604,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK13))))
    | ~ spl14_108 ),
    inference(unit_resulting_resolution,[],[f602,f97])).

fof(f602,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK13))))
    | ~ spl14_108 ),
    inference(avatar_component_clause,[],[f601])).

fof(f603,plain,
    ( spl14_108
    | ~ spl14_72
    | ~ spl14_106 ),
    inference(avatar_split_clause,[],[f587,f581,f423,f601])).

fof(f587,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK13))))
    | ~ spl14_72
    | ~ spl14_106 ),
    inference(unit_resulting_resolution,[],[f424,f582,f99])).

fof(f583,plain,
    ( spl14_106
    | ~ spl14_72 ),
    inference(avatar_split_clause,[],[f426,f423,f581])).

fof(f426,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK13))),sK4(sK4(sK13)))
    | ~ spl14_72 ),
    inference(unit_resulting_resolution,[],[f424,f100])).

fof(f574,plain,
    ( spl14_104
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_18 ),
    inference(avatar_split_clause,[],[f543,f199,f178,f150,f143,f136,f572])).

fof(f543,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK3),u1_struct_0(sK1))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_18 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f200,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1))
      | ~ r1_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f566,plain,
    ( spl14_102
    | spl14_1
    | ~ spl14_2
    | spl14_5
    | ~ spl14_12
    | ~ spl14_16 ),
    inference(avatar_split_clause,[],[f542,f192,f178,f150,f143,f136,f564])).

fof(f542,plain,
    ( m1_subset_1(sK9(sK0,sK1,sK2),u1_struct_0(sK1))
    | ~ spl14_1
    | ~ spl14_2
    | ~ spl14_5
    | ~ spl14_12
    | ~ spl14_16 ),
    inference(unit_resulting_resolution,[],[f137,f144,f151,f179,f193,f107])).

fof(f558,plain,
    ( spl14_100
    | ~ spl14_98 ),
    inference(avatar_split_clause,[],[f551,f548,f556])).

fof(f548,plain,
    ( spl14_98
  <=> l1_orders_2(sK4(sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_98])])).

fof(f551,plain,
    ( l1_struct_0(sK4(sK4(sK4(sK0))))
    | ~ spl14_98 ),
    inference(unit_resulting_resolution,[],[f549,f97])).

fof(f549,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK0))))
    | ~ spl14_98 ),
    inference(avatar_component_clause,[],[f548])).

fof(f550,plain,
    ( spl14_98
    | ~ spl14_56
    | ~ spl14_96 ),
    inference(avatar_split_clause,[],[f541,f535,f357,f548])).

fof(f541,plain,
    ( l1_orders_2(sK4(sK4(sK4(sK0))))
    | ~ spl14_56
    | ~ spl14_96 ),
    inference(unit_resulting_resolution,[],[f358,f536,f99])).

fof(f537,plain,
    ( spl14_96
    | ~ spl14_56 ),
    inference(avatar_split_clause,[],[f360,f357,f535])).

fof(f360,plain,
    ( l1_waybel_0(sK4(sK4(sK4(sK0))),sK4(sK4(sK0)))
    | ~ spl14_56 ),
    inference(unit_resulting_resolution,[],[f358,f100])).

fof(f529,plain,
    ( spl14_94
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f469,f178,f143,f527])).

fof(f527,plain,
    ( spl14_94
  <=> v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_94])])).

fof(f469,plain,
    ( v1_funct_2(u1_waybel_0(sK0,sK1),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f144,f179,f121])).

fof(f522,plain,
    ( spl14_92
    | ~ spl14_50
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f459,f456,f332,f520])).

fof(f520,plain,
    ( spl14_92
  <=> v1_funct_1(u1_waybel_0(sK4(sK1),sK4(sK4(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_92])])).

fof(f332,plain,
    ( spl14_50
  <=> l1_struct_0(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_50])])).

fof(f456,plain,
    ( spl14_80
  <=> l1_waybel_0(sK4(sK4(sK1)),sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_80])])).

fof(f459,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK1),sK4(sK4(sK1))))
    | ~ spl14_50
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f333,f457,f120])).

fof(f457,plain,
    ( l1_waybel_0(sK4(sK4(sK1)),sK4(sK1))
    | ~ spl14_80 ),
    inference(avatar_component_clause,[],[f456])).

fof(f333,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl14_50 ),
    inference(avatar_component_clause,[],[f332])).

fof(f515,plain,
    ( spl14_90
    | ~ spl14_44
    | ~ spl14_74 ),
    inference(avatar_split_clause,[],[f434,f431,f307,f513])).

fof(f513,plain,
    ( spl14_90
  <=> v1_funct_1(u1_waybel_0(sK4(sK12),sK4(sK4(sK12)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_90])])).

fof(f307,plain,
    ( spl14_44
  <=> l1_struct_0(sK4(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_44])])).

fof(f431,plain,
    ( spl14_74
  <=> l1_waybel_0(sK4(sK4(sK12)),sK4(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_74])])).

fof(f434,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK12),sK4(sK4(sK12))))
    | ~ spl14_44
    | ~ spl14_74 ),
    inference(unit_resulting_resolution,[],[f308,f432,f120])).

fof(f432,plain,
    ( l1_waybel_0(sK4(sK4(sK12)),sK4(sK12))
    | ~ spl14_74 ),
    inference(avatar_component_clause,[],[f431])).

fof(f308,plain,
    ( l1_struct_0(sK4(sK12))
    | ~ spl14_44 ),
    inference(avatar_component_clause,[],[f307])).

fof(f499,plain,
    ( spl14_88
    | ~ spl14_42
    | ~ spl14_58 ),
    inference(avatar_split_clause,[],[f409,f365,f298,f497])).

fof(f497,plain,
    ( spl14_88
  <=> v1_funct_1(u1_waybel_0(sK4(sK13),sK4(sK4(sK13)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_88])])).

fof(f298,plain,
    ( spl14_42
  <=> l1_struct_0(sK4(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_42])])).

fof(f365,plain,
    ( spl14_58
  <=> l1_waybel_0(sK4(sK4(sK13)),sK4(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_58])])).

fof(f409,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK13),sK4(sK4(sK13))))
    | ~ spl14_42
    | ~ spl14_58 ),
    inference(unit_resulting_resolution,[],[f299,f366,f120])).

fof(f366,plain,
    ( l1_waybel_0(sK4(sK4(sK13)),sK4(sK13))
    | ~ spl14_58 ),
    inference(avatar_component_clause,[],[f365])).

fof(f299,plain,
    ( l1_struct_0(sK4(sK13))
    | ~ spl14_42 ),
    inference(avatar_component_clause,[],[f298])).

fof(f492,plain,
    ( spl14_86
    | ~ spl14_38
    | ~ spl14_52 ),
    inference(avatar_split_clause,[],[f371,f340,f283,f490])).

fof(f490,plain,
    ( spl14_86
  <=> v1_funct_1(u1_waybel_0(sK4(sK0),sK4(sK4(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_86])])).

fof(f283,plain,
    ( spl14_38
  <=> l1_struct_0(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_38])])).

fof(f340,plain,
    ( spl14_52
  <=> l1_waybel_0(sK4(sK4(sK0)),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_52])])).

fof(f371,plain,
    ( v1_funct_1(u1_waybel_0(sK4(sK0),sK4(sK4(sK0))))
    | ~ spl14_38
    | ~ spl14_52 ),
    inference(unit_resulting_resolution,[],[f284,f341,f120])).

fof(f341,plain,
    ( l1_waybel_0(sK4(sK4(sK0)),sK4(sK0))
    | ~ spl14_52 ),
    inference(avatar_component_clause,[],[f340])).

fof(f284,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl14_38 ),
    inference(avatar_component_clause,[],[f283])).

fof(f484,plain,
    ( spl14_84
    | ~ spl14_82 ),
    inference(avatar_split_clause,[],[f468,f465,f482])).

fof(f465,plain,
    ( spl14_82
  <=> l1_orders_2(sK4(sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_82])])).

fof(f468,plain,
    ( l1_struct_0(sK4(sK4(sK1)))
    | ~ spl14_82 ),
    inference(unit_resulting_resolution,[],[f466,f97])).

fof(f466,plain,
    ( l1_orders_2(sK4(sK4(sK1)))
    | ~ spl14_82 ),
    inference(avatar_component_clause,[],[f465])).

fof(f467,plain,
    ( spl14_82
    | ~ spl14_50
    | ~ spl14_80 ),
    inference(avatar_split_clause,[],[f460,f456,f332,f465])).

fof(f460,plain,
    ( l1_orders_2(sK4(sK4(sK1)))
    | ~ spl14_50
    | ~ spl14_80 ),
    inference(unit_resulting_resolution,[],[f333,f457,f99])).

fof(f458,plain,
    ( spl14_80
    | ~ spl14_50 ),
    inference(avatar_split_clause,[],[f335,f332,f456])).

fof(f335,plain,
    ( l1_waybel_0(sK4(sK4(sK1)),sK4(sK1))
    | ~ spl14_50 ),
    inference(unit_resulting_resolution,[],[f333,f100])).

fof(f450,plain,
    ( spl14_78
    | ~ spl14_76 ),
    inference(avatar_split_clause,[],[f443,f440,f448])).

fof(f440,plain,
    ( spl14_76
  <=> l1_orders_2(sK4(sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_76])])).

fof(f443,plain,
    ( l1_struct_0(sK4(sK4(sK12)))
    | ~ spl14_76 ),
    inference(unit_resulting_resolution,[],[f441,f97])).

fof(f441,plain,
    ( l1_orders_2(sK4(sK4(sK12)))
    | ~ spl14_76 ),
    inference(avatar_component_clause,[],[f440])).

fof(f442,plain,
    ( spl14_76
    | ~ spl14_44
    | ~ spl14_74 ),
    inference(avatar_split_clause,[],[f435,f431,f307,f440])).

fof(f435,plain,
    ( l1_orders_2(sK4(sK4(sK12)))
    | ~ spl14_44
    | ~ spl14_74 ),
    inference(unit_resulting_resolution,[],[f308,f432,f99])).

fof(f433,plain,
    ( spl14_74
    | ~ spl14_44 ),
    inference(avatar_split_clause,[],[f310,f307,f431])).

fof(f310,plain,
    ( l1_waybel_0(sK4(sK4(sK12)),sK4(sK12))
    | ~ spl14_44 ),
    inference(unit_resulting_resolution,[],[f308,f100])).

fof(f425,plain,
    ( spl14_72
    | ~ spl14_70 ),
    inference(avatar_split_clause,[],[f418,f415,f423])).

fof(f415,plain,
    ( spl14_70
  <=> l1_orders_2(sK4(sK4(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).

fof(f418,plain,
    ( l1_struct_0(sK4(sK4(sK13)))
    | ~ spl14_70 ),
    inference(unit_resulting_resolution,[],[f416,f97])).

fof(f416,plain,
    ( l1_orders_2(sK4(sK4(sK13)))
    | ~ spl14_70 ),
    inference(avatar_component_clause,[],[f415])).

fof(f417,plain,
    ( spl14_70
    | ~ spl14_42
    | ~ spl14_58 ),
    inference(avatar_split_clause,[],[f410,f365,f298,f415])).

fof(f410,plain,
    ( l1_orders_2(sK4(sK4(sK13)))
    | ~ spl14_42
    | ~ spl14_58 ),
    inference(unit_resulting_resolution,[],[f299,f366,f99])).

fof(f408,plain,
    ( spl14_68
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f370,f315,f259,f406])).

fof(f406,plain,
    ( spl14_68
  <=> v1_funct_1(u1_waybel_0(sK1,sK4(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_68])])).

fof(f370,plain,
    ( v1_funct_1(u1_waybel_0(sK1,sK4(sK1)))
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f260,f316,f120])).

fof(f401,plain,
    ( spl14_66
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f372,f240,f207,f399])).

fof(f399,plain,
    ( spl14_66
  <=> v1_funct_1(u1_waybel_0(sK12,sK4(sK12))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_66])])).

fof(f372,plain,
    ( v1_funct_1(u1_waybel_0(sK12,sK4(sK12)))
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f208,f241,f120])).

fof(f394,plain,
    ( spl14_64
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f373,f224,f171,f392])).

fof(f392,plain,
    ( spl14_64
  <=> v1_funct_1(u1_waybel_0(sK13,sK4(sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_64])])).

fof(f373,plain,
    ( v1_funct_1(u1_waybel_0(sK13,sK4(sK13)))
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f172,f225,f120])).

fof(f387,plain,
    ( spl14_62
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f369,f217,f143,f385])).

fof(f385,plain,
    ( spl14_62
  <=> v1_funct_1(u1_waybel_0(sK0,sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_62])])).

fof(f369,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK4(sK0)))
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f144,f218,f120])).

fof(f380,plain,
    ( spl14_60
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f368,f178,f143,f378])).

fof(f368,plain,
    ( v1_funct_1(u1_waybel_0(sK0,sK1))
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f144,f179,f120])).

fof(f367,plain,
    ( spl14_58
    | ~ spl14_42 ),
    inference(avatar_split_clause,[],[f302,f298,f365])).

fof(f302,plain,
    ( l1_waybel_0(sK4(sK4(sK13)),sK4(sK13))
    | ~ spl14_42 ),
    inference(unit_resulting_resolution,[],[f299,f100])).

fof(f359,plain,
    ( spl14_56
    | ~ spl14_54 ),
    inference(avatar_split_clause,[],[f352,f349,f357])).

fof(f349,plain,
    ( spl14_54
  <=> l1_orders_2(sK4(sK4(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_54])])).

fof(f352,plain,
    ( l1_struct_0(sK4(sK4(sK0)))
    | ~ spl14_54 ),
    inference(unit_resulting_resolution,[],[f350,f97])).

fof(f350,plain,
    ( l1_orders_2(sK4(sK4(sK0)))
    | ~ spl14_54 ),
    inference(avatar_component_clause,[],[f349])).

fof(f351,plain,
    ( spl14_54
    | ~ spl14_38
    | ~ spl14_52 ),
    inference(avatar_split_clause,[],[f343,f340,f283,f349])).

fof(f343,plain,
    ( l1_orders_2(sK4(sK4(sK0)))
    | ~ spl14_38
    | ~ spl14_52 ),
    inference(unit_resulting_resolution,[],[f284,f341,f99])).

fof(f342,plain,
    ( spl14_52
    | ~ spl14_38 ),
    inference(avatar_split_clause,[],[f286,f283,f340])).

fof(f286,plain,
    ( l1_waybel_0(sK4(sK4(sK0)),sK4(sK0))
    | ~ spl14_38 ),
    inference(unit_resulting_resolution,[],[f284,f100])).

fof(f334,plain,
    ( spl14_50
    | ~ spl14_48 ),
    inference(avatar_split_clause,[],[f327,f323,f332])).

fof(f323,plain,
    ( spl14_48
  <=> l1_orders_2(sK4(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_48])])).

fof(f327,plain,
    ( l1_struct_0(sK4(sK1))
    | ~ spl14_48 ),
    inference(unit_resulting_resolution,[],[f324,f97])).

fof(f324,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl14_48 ),
    inference(avatar_component_clause,[],[f323])).

fof(f325,plain,
    ( spl14_48
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(avatar_split_clause,[],[f318,f315,f259,f323])).

fof(f318,plain,
    ( l1_orders_2(sK4(sK1))
    | ~ spl14_32
    | ~ spl14_46 ),
    inference(unit_resulting_resolution,[],[f260,f316,f99])).

fof(f317,plain,
    ( spl14_46
    | ~ spl14_32 ),
    inference(avatar_split_clause,[],[f262,f259,f315])).

fof(f262,plain,
    ( l1_waybel_0(sK4(sK1),sK1)
    | ~ spl14_32 ),
    inference(unit_resulting_resolution,[],[f260,f100])).

fof(f309,plain,
    ( spl14_44
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f301,f291,f307])).

fof(f291,plain,
    ( spl14_40
  <=> l1_orders_2(sK4(sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f301,plain,
    ( l1_struct_0(sK4(sK12))
    | ~ spl14_40 ),
    inference(unit_resulting_resolution,[],[f292,f97])).

fof(f292,plain,
    ( l1_orders_2(sK4(sK12))
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f291])).

fof(f300,plain,
    ( spl14_42
    | ~ spl14_36 ),
    inference(avatar_split_clause,[],[f278,f275,f298])).

fof(f275,plain,
    ( spl14_36
  <=> l1_orders_2(sK4(sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_36])])).

fof(f278,plain,
    ( l1_struct_0(sK4(sK13))
    | ~ spl14_36 ),
    inference(unit_resulting_resolution,[],[f276,f97])).

fof(f276,plain,
    ( l1_orders_2(sK4(sK13))
    | ~ spl14_36 ),
    inference(avatar_component_clause,[],[f275])).

fof(f293,plain,
    ( spl14_40
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(avatar_split_clause,[],[f246,f240,f207,f291])).

fof(f246,plain,
    ( l1_orders_2(sK4(sK12))
    | ~ spl14_20
    | ~ spl14_28 ),
    inference(unit_resulting_resolution,[],[f208,f241,f99])).

fof(f285,plain,
    ( spl14_38
    | ~ spl14_34 ),
    inference(avatar_split_clause,[],[f270,f267,f283])).

fof(f267,plain,
    ( spl14_34
  <=> l1_orders_2(sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_34])])).

fof(f270,plain,
    ( l1_struct_0(sK4(sK0))
    | ~ spl14_34 ),
    inference(unit_resulting_resolution,[],[f268,f97])).

fof(f268,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl14_34 ),
    inference(avatar_component_clause,[],[f267])).

fof(f277,plain,
    ( spl14_36
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(avatar_split_clause,[],[f245,f224,f171,f275])).

fof(f245,plain,
    ( l1_orders_2(sK4(sK13))
    | ~ spl14_10
    | ~ spl14_24 ),
    inference(unit_resulting_resolution,[],[f172,f225,f99])).

fof(f269,plain,
    ( spl14_34
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(avatar_split_clause,[],[f244,f217,f143,f267])).

fof(f244,plain,
    ( l1_orders_2(sK4(sK0))
    | ~ spl14_2
    | ~ spl14_22 ),
    inference(unit_resulting_resolution,[],[f144,f218,f99])).

fof(f261,plain,
    ( spl14_32
    | ~ spl14_30 ),
    inference(avatar_split_clause,[],[f254,f251,f259])).

fof(f254,plain,
    ( l1_struct_0(sK1)
    | ~ spl14_30 ),
    inference(unit_resulting_resolution,[],[f252,f97])).

fof(f253,plain,
    ( spl14_30
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(avatar_split_clause,[],[f243,f178,f143,f251])).

fof(f243,plain,
    ( l1_orders_2(sK1)
    | ~ spl14_2
    | ~ spl14_12 ),
    inference(unit_resulting_resolution,[],[f144,f179,f99])).

fof(f242,plain,
    ( spl14_28
    | ~ spl14_20 ),
    inference(avatar_split_clause,[],[f212,f207,f240])).

fof(f212,plain,
    ( l1_waybel_0(sK4(sK12),sK12)
    | ~ spl14_20 ),
    inference(unit_resulting_resolution,[],[f208,f100])).

fof(f234,plain,
    ( spl14_26
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f227,f185,f232])).

fof(f227,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl14_14 ),
    inference(unit_resulting_resolution,[],[f186,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',symmetry_r1_xboole_0)).

fof(f226,plain,
    ( spl14_24
    | ~ spl14_10 ),
    inference(avatar_split_clause,[],[f211,f171,f224])).

fof(f211,plain,
    ( l1_waybel_0(sK4(sK13),sK13)
    | ~ spl14_10 ),
    inference(unit_resulting_resolution,[],[f172,f100])).

fof(f219,plain,
    ( spl14_22
    | ~ spl14_2 ),
    inference(avatar_split_clause,[],[f210,f143,f217])).

fof(f210,plain,
    ( l1_waybel_0(sK4(sK0),sK0)
    | ~ spl14_2 ),
    inference(unit_resulting_resolution,[],[f144,f100])).

fof(f209,plain,
    ( spl14_20
    | ~ spl14_8 ),
    inference(avatar_split_clause,[],[f202,f164,f207])).

fof(f164,plain,
    ( spl14_8
  <=> l1_orders_2(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f202,plain,
    ( l1_struct_0(sK12)
    | ~ spl14_8 ),
    inference(unit_resulting_resolution,[],[f165,f97])).

fof(f165,plain,
    ( l1_orders_2(sK12)
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f164])).

fof(f201,plain,(
    spl14_18 ),
    inference(avatar_split_clause,[],[f95,f199])).

fof(f95,plain,(
    r1_waybel_0(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( r1_xboole_0(sK2,sK3)
    & r1_waybel_0(sK0,sK1,sK3)
    & r1_waybel_0(sK0,sK1,sK2)
    & l1_waybel_0(sK1,sK0)
    & v7_waybel_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f66,f65,f64])).

fof(f64,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) )
            & l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(sK0,X1,X3)
              & r1_waybel_0(sK0,X1,X2) )
          & l1_waybel_0(X1,sK0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X3,X2] :
            ( r1_xboole_0(X2,X3)
            & r1_waybel_0(X0,sK1,X3)
            & r1_waybel_0(X0,sK1,X2) )
        & l1_waybel_0(sK1,X0)
        & v7_waybel_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( r1_xboole_0(X2,X3)
          & r1_waybel_0(X0,X1,X3)
          & r1_waybel_0(X0,X1,X2) )
     => ( r1_xboole_0(sK2,sK3)
        & r1_waybel_0(X0,X1,sK3)
        & r1_waybel_0(X0,X1,sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( r1_xboole_0(X2,X3)
              & r1_waybel_0(X0,X1,X3)
              & r1_waybel_0(X0,X1,X2) )
          & l1_waybel_0(X1,X0)
          & v7_waybel_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ~ ( r1_xboole_0(X2,X3)
                  & r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2,X3] :
                ~ ( r1_xboole_0(X2,X3)
                  & r1_waybel_0(X0,X1,X3)
                  & r1_waybel_0(X0,X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2,X3] :
              ~ ( r1_xboole_0(X2,X3)
                & r1_waybel_0(X0,X1,X3)
                & r1_waybel_0(X0,X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',t26_yellow_6)).

fof(f194,plain,(
    spl14_16 ),
    inference(avatar_split_clause,[],[f94,f192])).

fof(f94,plain,(
    r1_waybel_0(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f187,plain,(
    spl14_14 ),
    inference(avatar_split_clause,[],[f96,f185])).

fof(f96,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f180,plain,(
    spl14_12 ),
    inference(avatar_split_clause,[],[f93,f178])).

fof(f93,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f173,plain,(
    spl14_10 ),
    inference(avatar_split_clause,[],[f131,f171])).

fof(f131,plain,(
    l1_struct_0(sK13) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    l1_struct_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f19,f87])).

fof(f87,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK13) ),
    introduced(choice_axiom,[])).

fof(f19,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',existence_l1_struct_0)).

fof(f166,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f130,f164])).

fof(f130,plain,(
    l1_orders_2(sK12) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    l1_orders_2(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f18,f85])).

fof(f85,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK12) ),
    introduced(choice_axiom,[])).

fof(f18,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/yellow_6__t26_yellow_6.p',existence_l1_orders_2)).

fof(f159,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f92,f157])).

fof(f92,plain,(
    v7_waybel_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f152,plain,(
    ~ spl14_5 ),
    inference(avatar_split_clause,[],[f91,f150])).

fof(f91,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f145,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f90,f143])).

fof(f90,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f138,plain,(
    ~ spl14_1 ),
    inference(avatar_split_clause,[],[f89,f136])).

fof(f89,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
