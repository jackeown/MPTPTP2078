%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1100+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:06 EST 2020

% Result     : Theorem 44.80s
% Output     : Refutation 45.88s
% Verified   : 
% Statistics : Number of formulae       : 2255 (13142 expanded)
%              Number of leaves         :  382 (4240 expanded)
%              Depth                    :   19
%              Number of atoms          : 5931 (35850 expanded)
%              Number of equality atoms :  515 (6982 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29310,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2247,f2252,f2257,f2262,f2267,f2272,f2277,f2282,f2287,f2292,f2297,f2302,f2309,f2314,f2322,f2327,f2335,f2340,f2384,f2393,f2397,f2419,f2435,f2440,f2477,f2491,f2496,f2505,f2510,f2585,f2593,f2607,f2735,f3066,f3074,f3083,f3092,f3097,f3119,f3155,f3399,f3408,f3584,f3609,f3631,f3644,f3661,f3667,f3670,f3690,f3793,f4930,f5331,f5348,f5349,f5350,f5755,f5760,f5776,f5778,f5780,f5782,f5811,f5816,f5819,f5821,f5827,f5861,f5866,f5869,f5871,f5877,f6188,f6192,f6196,f6414,f6656,f6691,f6850,f6856,f6857,f6859,f6863,f6864,f6868,f6869,f6873,f6874,f6875,f6876,f6908,f6912,f6916,f7034,f7755,f7759,f7763,f8348,f8354,f8360,f8366,f8481,f8559,f8566,f8572,f8578,f8584,f8664,f8834,f8849,f9091,f9477,f9590,f9730,f9735,f9740,f9745,f9788,f9793,f9801,f9802,f9807,f9808,f9809,f9814,f9816,f9817,f9818,f9819,f9820,f9821,f9822,f10025,f10030,f10035,f10040,f10080,f10085,f10090,f10091,f10096,f10097,f10098,f10103,f10105,f10106,f10107,f10108,f10109,f10110,f10111,f11208,f11212,f11216,f11217,f11262,f11277,f11279,f11283,f11286,f11869,f11875,f11881,f11888,f11938,f11944,f11950,f11957,f12434,f12438,f12442,f12446,f12450,f12555,f12559,f12563,f12567,f12571,f12629,f12705,f12709,f12713,f12717,f12721,f12954,f12958,f12962,f13983,f13988,f13992,f13996,f14002,f14005,f14009,f14013,f14017,f14021,f14025,f14029,f14033,f14037,f14041,f14045,f14049,f14053,f14057,f14061,f14065,f14069,f14073,f14077,f14081,f14085,f14089,f14093,f14097,f14101,f14105,f14109,f14113,f14117,f14121,f14125,f14129,f14133,f14138,f14143,f14145,f14150,f14155,f14161,f14163,f14165,f14167,f14169,f14171,f14176,f14180,f14184,f14188,f14192,f14196,f14200,f14204,f14208,f14212,f14216,f14220,f14224,f14232,f14287,f14291,f14293,f14298,f14302,f14304,f14305,f14307,f14314,f14319,f14320,f14324,f14325,f14326,f14330,f14334,f14338,f14342,f14344,f14345,f14346,f14350,f14354,f14359,f14363,f14367,f14368,f14373,f14378,f14379,f14380,f14381,f14382,f14383,f14388,f14389,f14394,f14399,f14404,f14405,f14406,f14411,f14416,f14421,f14426,f14431,f14436,f14440,f14444,f14472,f14488,f14578,f14583,f14588,f14593,f14598,f14603,f14608,f14613,f14618,f14623,f14628,f14634,f14639,f14640,f14645,f14651,f14656,f14657,f14660,f16210,f16214,f16218,f16219,f18005,f18012,f18023,f18127,f18128,f18129,f18130,f18131,f18132,f18133,f18134,f18135,f18136,f18137,f18138,f18139,f18140,f18141,f18142,f18143,f18144,f18145,f18146,f18147,f18148,f18149,f18150,f18151,f18152,f18153,f18154,f18155,f18156,f18157,f18158,f18159,f18160,f18161,f18162,f18163,f18164,f18165,f18166,f18167,f18168,f18169,f18170,f18171,f18172,f18173,f18174,f18175,f18176,f18177,f18178,f18179,f18180,f18181,f18182,f18183,f18184,f18185,f18186,f18188,f19587,f19592,f19596,f19602,f19611,f22166,f22174,f22178,f22182,f22189,f22282,f22287,f22294,f22298,f22300,f22302,f22305,f22309,f22312,f24055,f24060,f24142,f24147,f24152,f24157,f24162,f24167,f24170,f24172,f24174,f24176,f24183,f24185,f24187,f25581,f27590,f27600,f27609,f27630,f27635,f27638,f27642,f27648,f27653,f27661,f27678,f27681,f27684,f27687,f27720,f27829,f27881,f27897,f27899,f27935,f27947,f27965,f27968,f27971,f27989,f28004,f28030,f28032,f28034,f28039,f28042,f28044,f28046,f28048,f28060,f28073,f28077,f28084,f28086,f28089,f28092,f28096,f28101,f28106,f28108,f28130,f28135,f28142,f28169,f28176,f28182,f28190,f28218,f28221,f28236,f28247,f28252,f28293,f28301,f28303,f28307,f28309,f28322,f28328,f28331,f28333,f28772,f28775,f28778,f28780,f28783,f28786,f28789,f28792,f28795,f28798,f28813,f28816,f28819,f28822,f28825,f28828,f28831,f28834,f28837,f28840,f28842,f28852,f28888,f28915,f28918,f28920,f28922,f28988,f29013,f29017,f29027,f29034,f29067,f29080,f29082,f29085,f29304,f29307])).

fof(f29307,plain,
    ( spl33_1
    | ~ spl33_10
    | ~ spl33_19
    | ~ spl33_112 ),
    inference(avatar_contradiction_clause,[],[f29306])).

fof(f29306,plain,
    ( $false
    | spl33_1
    | ~ spl33_10
    | ~ spl33_19
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f29305,f2291])).

fof(f2291,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl33_10 ),
    inference(avatar_component_clause,[],[f2289])).

fof(f2289,plain,
    ( spl33_10
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_10])])).

fof(f29305,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_1
    | ~ spl33_19
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f29292,f2383])).

fof(f2383,plain,
    ( sP0(sK2)
    | ~ spl33_19 ),
    inference(avatar_component_clause,[],[f2381])).

fof(f2381,plain,
    ( spl33_19
  <=> sP0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_19])])).

fof(f29292,plain,
    ( ~ sP0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | spl33_1
    | ~ spl33_112 ),
    inference(resolution,[],[f29280,f2350])).

fof(f2350,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_pre_topc(sK2))
        | ~ v1_xboole_0(X0) )
    | spl33_1 ),
    inference(superposition,[],[f2246,f2152])).

fof(f2152,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1859])).

fof(f1859,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f2246,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK2))
    | spl33_1 ),
    inference(avatar_component_clause,[],[f2244])).

fof(f2244,plain,
    ( spl33_1
  <=> r2_hidden(k1_xboole_0,u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_1])])).

fof(f29280,plain,
    ( ! [X12] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X12))
        | ~ sP0(X12) )
    | ~ spl33_112 ),
    inference(forward_demodulation,[],[f29279,f9813])).

fof(f9813,plain,
    ( k1_xboole_0 = k3_tarski(k1_xboole_0)
    | ~ spl33_112 ),
    inference(avatar_component_clause,[],[f9811])).

fof(f9811,plain,
    ( spl33_112
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_112])])).

fof(f29279,plain,(
    ! [X12] :
      ( r2_hidden(k3_tarski(k1_xboole_0),u1_pre_topc(X12))
      | ~ sP0(X12) ) ),
    inference(subsumption_resolution,[],[f29235,f2079])).

fof(f2079,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f29235,plain,(
    ! [X12] :
      ( ~ r1_tarski(k1_xboole_0,u1_pre_topc(X12))
      | r2_hidden(k3_tarski(k1_xboole_0),u1_pre_topc(X12))
      | ~ sP0(X12) ) ),
    inference(resolution,[],[f5712,f2078])).

fof(f2078,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f5712,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | r2_hidden(k3_tarski(X1),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(duplicate_literal_removal,[],[f5711])).

fof(f5711,plain,(
    ! [X0,X1] :
      ( r2_hidden(k3_tarski(X1),u1_pre_topc(X0))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(superposition,[],[f2085,f2222])).

fof(f2222,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1901])).

fof(f1901,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f2085,plain,(
    ! [X6,X0] :
      ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
      | ~ r1_tarski(X6,u1_pre_topc(X0))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f1965])).

fof(f1965,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK19(X0),sK20(X0)),u1_pre_topc(X0))
          & r2_hidden(sK20(X0),u1_pre_topc(X0))
          & r2_hidden(sK19(X0),u1_pre_topc(X0))
          & m1_subset_1(sK20(X0),k1_zfmisc_1(u1_struct_0(X0)))
          & m1_subset_1(sK19(X0),k1_zfmisc_1(u1_struct_0(X0))) )
        | ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK21(X0)),u1_pre_topc(X0))
          & r1_tarski(sK21(X0),u1_pre_topc(X0))
          & m1_subset_1(sK21(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19,sK20,sK21])],[f1961,f1964,f1963,f1962])).

fof(f1962,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
              & r2_hidden(X2,u1_pre_topc(X0))
              & r2_hidden(X1,u1_pre_topc(X0))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ? [X2] :
            ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK19(X0),X2),u1_pre_topc(X0))
            & r2_hidden(X2,u1_pre_topc(X0))
            & r2_hidden(sK19(X0),u1_pre_topc(X0))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK19(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1963,plain,(
    ! [X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK19(X0),X2),u1_pre_topc(X0))
          & r2_hidden(X2,u1_pre_topc(X0))
          & r2_hidden(sK19(X0),u1_pre_topc(X0))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),sK19(X0),sK20(X0)),u1_pre_topc(X0))
        & r2_hidden(sK20(X0),u1_pre_topc(X0))
        & r2_hidden(sK19(X0),u1_pre_topc(X0))
        & m1_subset_1(sK20(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1964,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
          & r1_tarski(X3,u1_pre_topc(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
     => ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),sK21(X0)),u1_pre_topc(X0))
        & r1_tarski(sK21(X0),u1_pre_topc(X0))
        & m1_subset_1(sK21(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ),
    introduced(choice_axiom,[])).

fof(f1961,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X4] :
              ( ! [X5] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X4,X5),u1_pre_topc(X0))
                  | ~ r2_hidden(X5,u1_pre_topc(X0))
                  | ~ r2_hidden(X4,u1_pre_topc(X0))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X6] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X6),u1_pre_topc(X0))
              | ~ r1_tarski(X6,u1_pre_topc(X0))
              | ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(rectify,[],[f1960])).

fof(f1960,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(flattening,[],[f1959])).

fof(f1959,plain,(
    ! [X0] :
      ( ( sP0(X0)
        | ? [X1] :
            ( ? [X2] :
                ( ~ r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                & r2_hidden(X2,u1_pre_topc(X0))
                & r2_hidden(X1,u1_pre_topc(X0))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        | ? [X3] :
            ( ~ r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            & r1_tarski(X3,u1_pre_topc(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        | ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
      & ( ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) )
        | ~ sP0(X0) ) ) ),
    inference(nnf_transformation,[],[f1907])).

fof(f1907,plain,(
    ! [X0] :
      ( sP0(X0)
    <=> ( ! [X1] :
            ( ! [X2] :
                ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                | ~ r2_hidden(X2,u1_pre_topc(X0))
                | ~ r2_hidden(X1,u1_pre_topc(X0))
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & ! [X3] :
            ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
            | ~ r1_tarski(X3,u1_pre_topc(X0))
            | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
        & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f29304,plain,
    ( spl33_1
    | ~ spl33_19
    | ~ spl33_112 ),
    inference(avatar_contradiction_clause,[],[f29303])).

fof(f29303,plain,
    ( $false
    | spl33_1
    | ~ spl33_19
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f29291,f2383])).

fof(f29291,plain,
    ( ~ sP0(sK2)
    | spl33_1
    | ~ spl33_112 ),
    inference(resolution,[],[f29280,f2246])).

fof(f29085,plain,
    ( ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29084])).

fof(f29084,plain,
    ( $false
    | ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f29083,f2291])).

fof(f29083,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_98
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27565,f25580])).

fof(f25580,plain,
    ( ! [X471] : k1_xboole_0 = X471
    | ~ spl33_287 ),
    inference(avatar_component_clause,[],[f25579])).

fof(f25579,plain,
    ( spl33_287
  <=> ! [X471] : k1_xboole_0 = X471 ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_287])])).

fof(f27565,plain,
    ( ~ v1_xboole_0(sK22(k1_xboole_0))
    | spl33_98
    | ~ spl33_287 ),
    inference(superposition,[],[f8833,f25580])).

fof(f8833,plain,
    ( ~ v1_xboole_0(sK22(sK28(u1_pre_topc(sK2))))
    | spl33_98 ),
    inference(avatar_component_clause,[],[f8831])).

fof(f8831,plain,
    ( spl33_98
  <=> v1_xboole_0(sK22(sK28(u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_98])])).

fof(f29082,plain,
    ( ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29081])).

fof(f29081,plain,
    ( $false
    | ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27564,f2291])).

fof(f27564,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_99
    | ~ spl33_287 ),
    inference(superposition,[],[f8848,f25580])).

fof(f8848,plain,
    ( ~ v1_xboole_0(sK28(u1_pre_topc(sK2)))
    | spl33_99 ),
    inference(avatar_component_clause,[],[f8846])).

fof(f8846,plain,
    ( spl33_99
  <=> v1_xboole_0(sK28(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_99])])).

fof(f29080,plain,
    ( ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29079])).

fof(f29079,plain,
    ( $false
    | ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f29078,f2291])).

fof(f29078,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_100
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27563,f25580])).

fof(f27563,plain,
    ( ~ v1_xboole_0(sK27(k1_xboole_0))
    | spl33_100
    | ~ spl33_287 ),
    inference(superposition,[],[f9090,f25580])).

fof(f9090,plain,
    ( ~ v1_xboole_0(sK27(sK28(u1_pre_topc(sK2))))
    | spl33_100 ),
    inference(avatar_component_clause,[],[f9088])).

fof(f9088,plain,
    ( spl33_100
  <=> v1_xboole_0(sK27(sK28(u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_100])])).

fof(f29067,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29066])).

fof(f29066,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f29065,f2355])).

fof(f2355,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f2036,f2228])).

fof(f2228,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2050])).

fof(f2050,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f1944])).

fof(f1944,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f1943])).

fof(f1943,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f329])).

fof(f329,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f2036,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f29065,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27546,f25580])).

fof(f27546,plain,
    ( ! [X0] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f12170,f25580])).

fof(f12170,plain,(
    ! [X36] : r2_hidden(k3_tarski(sK28(k1_zfmisc_1(X36))),k1_zfmisc_1(X36)) ),
    inference(subsumption_resolution,[],[f12165,f2160])).

fof(f2160,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f12165,plain,(
    ! [X36] :
      ( v1_xboole_0(k1_zfmisc_1(X36))
      | r2_hidden(k3_tarski(sK28(k1_zfmisc_1(X36))),k1_zfmisc_1(X36)) ) ),
    inference(resolution,[],[f9867,f2132])).

fof(f2132,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1844])).

fof(f1844,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1843])).

fof(f1843,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f599])).

fof(f599,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f9867,plain,(
    ! [X51] : m1_subset_1(k3_tarski(sK28(k1_zfmisc_1(X51))),k1_zfmisc_1(X51)) ),
    inference(subsumption_resolution,[],[f9858,f2160])).

fof(f9858,plain,(
    ! [X51] :
      ( m1_subset_1(k3_tarski(sK28(k1_zfmisc_1(X51))),k1_zfmisc_1(X51))
      | v1_xboole_0(k1_zfmisc_1(X51)) ) ),
    inference(resolution,[],[f3576,f2156])).

fof(f2156,plain,(
    ! [X0] :
      ( m1_subset_1(sK28(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1985])).

fof(f1985,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK28(X0))
        & m1_subset_1(sK28(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK28])],[f1863,f1984])).

fof(f1984,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK28(X0))
        & m1_subset_1(sK28(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1863,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f489])).

fof(f489,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f3576,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f3575])).

fof(f3575,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f2221,f2222])).

fof(f2221,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f1900])).

fof(f1900,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f29034,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29033])).

fof(f29033,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f29032,f2355])).

fof(f29032,plain,
    ( r2_hidden(sK27(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27504,f25580])).

fof(f27504,plain,
    ( ! [X0] : r2_hidden(sK27(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f9079,f25580])).

fof(f9079,plain,(
    ! [X20] : r2_hidden(sK27(sK28(k1_tarski(X20))),k1_zfmisc_1(X20)) ),
    inference(subsumption_resolution,[],[f9049,f2161])).

fof(f2161,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f293])).

fof(f293,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f9049,plain,(
    ! [X20] :
      ( v1_xboole_0(k1_tarski(X20))
      | r2_hidden(sK27(sK28(k1_tarski(X20))),k1_zfmisc_1(X20)) ) ),
    inference(resolution,[],[f8539,f2868])).

fof(f2868,plain,(
    ! [X33,X32] :
      ( ~ r2_hidden(X32,k1_tarski(X33))
      | r2_hidden(X32,k1_zfmisc_1(X33)) ) ),
    inference(resolution,[],[f2015,f2200])).

fof(f2200,plain,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f434])).

fof(f434,axiom,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

fof(f2015,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1921])).

fof(f1921,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK5(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f1919,f1920])).

fof(f1920,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK5(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1919,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f1918])).

fof(f1918,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1780])).

fof(f1780,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f8539,plain,(
    ! [X31] :
      ( r2_hidden(sK27(sK28(X31)),X31)
      | v1_xboole_0(X31) ) ),
    inference(duplicate_literal_removal,[],[f8531])).

fof(f8531,plain,(
    ! [X31] :
      ( v1_xboole_0(X31)
      | v1_xboole_0(X31)
      | r2_hidden(sK27(sK28(X31)),X31) ) ),
    inference(resolution,[],[f8304,f2132])).

fof(f8304,plain,(
    ! [X23] :
      ( m1_subset_1(sK27(sK28(X23)),X23)
      | v1_xboole_0(X23) ) ),
    inference(subsumption_resolution,[],[f8299,f2157])).

fof(f2157,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK28(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1985])).

fof(f8299,plain,(
    ! [X23] :
      ( m1_subset_1(sK27(sK28(X23)),X23)
      | v1_xboole_0(X23)
      | v1_xboole_0(sK28(X23)) ) ),
    inference(resolution,[],[f3110,f2146])).

fof(f2146,plain,(
    ! [X0] :
      ( r2_hidden(sK27(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1983])).

fof(f1983,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK27(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f1981,f1982])).

fof(f1982,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK27(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1981,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f1980])).

fof(f1980,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f3110,plain,(
    ! [X30,X29] :
      ( ~ r2_hidden(X29,sK28(X30))
      | m1_subset_1(X29,X30)
      | v1_xboole_0(X30) ) ),
    inference(resolution,[],[f2007,f2156])).

fof(f2007,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1777])).

fof(f1777,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f1776])).

fof(f1776,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f618])).

fof(f618,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f29027,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29026])).

fof(f29026,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f29025,f2355])).

fof(f29025,plain,
    ( r2_hidden(sK22(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27497,f25580])).

fof(f27497,plain,
    ( ! [X0] : r2_hidden(sK22(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f8822,f25580])).

fof(f8822,plain,(
    ! [X18] : r2_hidden(sK22(sK28(k1_tarski(X18))),k1_zfmisc_1(X18)) ),
    inference(subsumption_resolution,[],[f8795,f2161])).

fof(f8795,plain,(
    ! [X18] :
      ( v1_xboole_0(k1_tarski(X18))
      | r2_hidden(sK22(sK28(k1_tarski(X18))),k1_zfmisc_1(X18)) ) ),
    inference(resolution,[],[f8327,f2868])).

fof(f8327,plain,(
    ! [X31] :
      ( r2_hidden(sK22(sK28(X31)),X31)
      | v1_xboole_0(X31) ) ),
    inference(duplicate_literal_removal,[],[f8320])).

fof(f8320,plain,(
    ! [X31] :
      ( v1_xboole_0(X31)
      | v1_xboole_0(X31)
      | r2_hidden(sK22(sK28(X31)),X31) ) ),
    inference(resolution,[],[f8303,f2132])).

fof(f8303,plain,(
    ! [X22] :
      ( m1_subset_1(sK22(sK28(X22)),X22)
      | v1_xboole_0(X22) ) ),
    inference(subsumption_resolution,[],[f8298,f2157])).

fof(f8298,plain,(
    ! [X22] :
      ( m1_subset_1(sK22(sK28(X22)),X22)
      | v1_xboole_0(X22)
      | v1_xboole_0(sK28(X22)) ) ),
    inference(resolution,[],[f3110,f2761])).

fof(f2761,plain,(
    ! [X12] :
      ( r2_hidden(sK22(X12),X12)
      | v1_xboole_0(X12) ) ),
    inference(resolution,[],[f2132,f2108])).

fof(f2108,plain,(
    ! [X0] : m1_subset_1(sK22(X0),X0) ),
    inference(cnf_transformation,[],[f1968])).

fof(f1968,plain,(
    ! [X0] : m1_subset_1(sK22(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f474,f1967])).

fof(f1967,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK22(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f29017,plain,
    ( ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29016])).

fof(f29016,plain,
    ( $false
    | ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27478,f2291])).

fof(f27478,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_100
    | ~ spl33_287 ),
    inference(superposition,[],[f9090,f25580])).

fof(f29013,plain,
    ( ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f29012])).

fof(f29012,plain,
    ( $false
    | ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27455,f2291])).

fof(f27455,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_42
    | ~ spl33_287 ),
    inference(superposition,[],[f3096,f25580])).

fof(f3096,plain,
    ( ~ v1_xboole_0(sK27(u1_pre_topc(sK2)))
    | spl33_42 ),
    inference(avatar_component_clause,[],[f3094])).

fof(f3094,plain,
    ( spl33_42
  <=> v1_xboole_0(sK27(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_42])])).

fof(f28988,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28987])).

fof(f28987,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28986,f2355])).

fof(f28986,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27361,f25580])).

fof(f27361,plain,
    ( ! [X0] : r2_hidden(k3_tarski(k1_xboole_0),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f12143,f25580])).

fof(f12143,plain,(
    ! [X36] : r2_hidden(k3_tarski(sK26(k1_zfmisc_1(X36))),k1_zfmisc_1(X36)) ),
    inference(subsumption_resolution,[],[f12136,f2160])).

fof(f12136,plain,(
    ! [X36] :
      ( v1_xboole_0(k1_zfmisc_1(X36))
      | r2_hidden(k3_tarski(sK26(k1_zfmisc_1(X36))),k1_zfmisc_1(X36)) ) ),
    inference(resolution,[],[f9855,f2132])).

fof(f9855,plain,(
    ! [X48] : m1_subset_1(k3_tarski(sK26(k1_zfmisc_1(X48))),k1_zfmisc_1(X48)) ),
    inference(resolution,[],[f3576,f2143])).

fof(f2143,plain,(
    ! [X0] : m1_subset_1(sK26(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f1979])).

fof(f1979,plain,(
    ! [X0] :
      ( v1_xboole_0(sK26(X0))
      & m1_subset_1(sK26(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26])],[f490,f1978])).

fof(f1978,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK26(X0))
        & m1_subset_1(sK26(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f28922,plain,
    ( spl33_9
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28921])).

fof(f28921,plain,
    ( $false
    | spl33_9
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27263,f2291])).

fof(f27263,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_9
    | ~ spl33_287 ),
    inference(superposition,[],[f2286,f25580])).

fof(f2286,plain,
    ( ~ v1_xboole_0(sK25)
    | spl33_9 ),
    inference(avatar_component_clause,[],[f2284])).

fof(f2284,plain,
    ( spl33_9
  <=> v1_xboole_0(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_9])])).

fof(f28920,plain,
    ( spl33_7
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28919])).

fof(f28919,plain,
    ( $false
    | spl33_7
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27258,f2291])).

fof(f27258,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_7
    | ~ spl33_287 ),
    inference(superposition,[],[f2276,f25580])).

fof(f2276,plain,
    ( ~ v1_xboole_0(sK23)
    | spl33_7 ),
    inference(avatar_component_clause,[],[f2274])).

fof(f2274,plain,
    ( spl33_7
  <=> v1_xboole_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_7])])).

fof(f28918,plain,
    ( ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28917])).

fof(f28917,plain,
    ( $false
    | ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27257,f2291])).

fof(f27257,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_98
    | ~ spl33_287 ),
    inference(superposition,[],[f8833,f25580])).

fof(f28915,plain,
    ( ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28914])).

fof(f28914,plain,
    ( $false
    | ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27236,f2291])).

fof(f27236,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_41
    | ~ spl33_287 ),
    inference(superposition,[],[f3091,f25580])).

fof(f3091,plain,
    ( ~ v1_xboole_0(sK22(u1_pre_topc(sK2)))
    | spl33_41 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f3089,plain,
    ( spl33_41
  <=> v1_xboole_0(sK22(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_41])])).

fof(f28888,plain,
    ( ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28887])).

fof(f28887,plain,
    ( $false
    | ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27136,f2291])).

fof(f27136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_39
    | ~ spl33_287 ),
    inference(superposition,[],[f3082,f25580])).

fof(f3082,plain,
    ( ~ v1_xboole_0(sK15(u1_pre_topc(sK2)))
    | spl33_39 ),
    inference(avatar_component_clause,[],[f3080])).

fof(f3080,plain,
    ( spl33_39
  <=> v1_xboole_0(sK15(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_39])])).

fof(f28852,plain,
    ( ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28851])).

fof(f28851,plain,
    ( $false
    | ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27064,f2291])).

fof(f27064,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_278
    | ~ spl33_287 ),
    inference(superposition,[],[f24059,f25580])).

fof(f24059,plain,
    ( ~ v1_xboole_0(sK6(u1_pre_topc(sK2),k1_xboole_0))
    | spl33_278 ),
    inference(avatar_component_clause,[],[f24057])).

fof(f24057,plain,
    ( spl33_278
  <=> v1_xboole_0(sK6(u1_pre_topc(sK2),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_278])])).

fof(f28842,plain,
    ( ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28841])).

fof(f28841,plain,
    ( $false
    | ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27035,f2291])).

fof(f27035,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_37
    | ~ spl33_287 ),
    inference(superposition,[],[f3073,f25580])).

fof(f3073,plain,
    ( ~ v1_xboole_0(sK3(u1_pre_topc(sK2)))
    | spl33_37 ),
    inference(avatar_component_clause,[],[f3071])).

fof(f3071,plain,
    ( spl33_37
  <=> v1_xboole_0(sK3(u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_37])])).

fof(f28840,plain,
    ( ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28839])).

fof(f28839,plain,
    ( $false
    | ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28838,f2291])).

fof(f28838,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_278
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27013,f25580])).

fof(f27013,plain,
    ( ~ v1_xboole_0(sK6(u1_pre_topc(k1_xboole_0),k1_xboole_0))
    | spl33_278
    | ~ spl33_287 ),
    inference(superposition,[],[f24059,f25580])).

fof(f28837,plain,
    ( ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28836])).

fof(f28836,plain,
    ( $false
    | ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28835,f2291])).

fof(f28835,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_100
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27012,f25580])).

fof(f27012,plain,
    ( ~ v1_xboole_0(sK27(sK28(u1_pre_topc(k1_xboole_0))))
    | spl33_100
    | ~ spl33_287 ),
    inference(superposition,[],[f9090,f25580])).

fof(f28834,plain,
    ( ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28833])).

fof(f28833,plain,
    ( $false
    | ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28832,f2291])).

fof(f28832,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_99
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27011,f25580])).

fof(f27011,plain,
    ( ~ v1_xboole_0(sK28(u1_pre_topc(k1_xboole_0)))
    | spl33_99
    | ~ spl33_287 ),
    inference(superposition,[],[f8848,f25580])).

fof(f28831,plain,
    ( ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28830])).

fof(f28830,plain,
    ( $false
    | ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28829,f2291])).

fof(f28829,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_98
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27010,f25580])).

fof(f27010,plain,
    ( ~ v1_xboole_0(sK22(sK28(u1_pre_topc(k1_xboole_0))))
    | spl33_98
    | ~ spl33_287 ),
    inference(superposition,[],[f8833,f25580])).

fof(f28828,plain,
    ( ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28827])).

fof(f28827,plain,
    ( $false
    | ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28826,f2291])).

fof(f28826,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_42
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27009,f25580])).

fof(f27009,plain,
    ( ~ v1_xboole_0(sK27(u1_pre_topc(k1_xboole_0)))
    | spl33_42
    | ~ spl33_287 ),
    inference(superposition,[],[f3096,f25580])).

fof(f28825,plain,
    ( ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28824])).

fof(f28824,plain,
    ( $false
    | ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28823,f2291])).

fof(f28823,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_41
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27008,f25580])).

fof(f27008,plain,
    ( ~ v1_xboole_0(sK22(u1_pre_topc(k1_xboole_0)))
    | spl33_41
    | ~ spl33_287 ),
    inference(superposition,[],[f3091,f25580])).

fof(f28822,plain,
    ( ~ spl33_10
    | spl33_40
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28821])).

fof(f28821,plain,
    ( $false
    | ~ spl33_10
    | spl33_40
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28820,f2291])).

fof(f28820,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_40
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27007,f25580])).

fof(f27007,plain,
    ( ~ v1_xboole_0(u1_pre_topc(k1_xboole_0))
    | spl33_40
    | ~ spl33_287 ),
    inference(superposition,[],[f3086,f25580])).

fof(f3086,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK2))
    | spl33_40 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f3085,plain,
    ( spl33_40
  <=> v1_xboole_0(u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_40])])).

fof(f28819,plain,
    ( ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28818])).

fof(f28818,plain,
    ( $false
    | ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28817,f2291])).

fof(f28817,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_39
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27006,f25580])).

fof(f27006,plain,
    ( ~ v1_xboole_0(sK15(u1_pre_topc(k1_xboole_0)))
    | spl33_39
    | ~ spl33_287 ),
    inference(superposition,[],[f3082,f25580])).

fof(f28816,plain,
    ( ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28815])).

fof(f28815,plain,
    ( $false
    | ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28814,f2291])).

fof(f28814,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_37
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27005,f25580])).

fof(f27005,plain,
    ( ~ v1_xboole_0(sK3(u1_pre_topc(k1_xboole_0)))
    | spl33_37
    | ~ spl33_287 ),
    inference(superposition,[],[f3073,f25580])).

fof(f28813,plain,
    ( ~ spl33_10
    | spl33_35
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28812])).

fof(f28812,plain,
    ( $false
    | ~ spl33_10
    | spl33_35
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28811,f2291])).

fof(f28811,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_35
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f27004,f25580])).

fof(f27004,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_xboole_0))
    | spl33_35
    | ~ spl33_287 ),
    inference(superposition,[],[f3065,f25580])).

fof(f3065,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl33_35 ),
    inference(avatar_component_clause,[],[f3063])).

fof(f3063,plain,
    ( spl33_35
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_35])])).

fof(f28798,plain,
    ( ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28797])).

fof(f28797,plain,
    ( $false
    | ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28796,f2291])).

fof(f28796,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_278
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26973,f25580])).

fof(f26973,plain,
    ( ~ v1_xboole_0(sK6(k1_xboole_0,k1_xboole_0))
    | spl33_278
    | ~ spl33_287 ),
    inference(superposition,[],[f24059,f25580])).

fof(f28795,plain,
    ( ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28794])).

fof(f28794,plain,
    ( $false
    | ~ spl33_10
    | spl33_100
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28793,f2291])).

fof(f28793,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_100
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26972,f25580])).

fof(f26972,plain,
    ( ~ v1_xboole_0(sK27(sK28(k1_xboole_0)))
    | spl33_100
    | ~ spl33_287 ),
    inference(superposition,[],[f9090,f25580])).

fof(f28792,plain,
    ( ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28791])).

fof(f28791,plain,
    ( $false
    | ~ spl33_10
    | spl33_99
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28790,f2291])).

fof(f28790,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_99
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26971,f25580])).

fof(f26971,plain,
    ( ~ v1_xboole_0(sK28(k1_xboole_0))
    | spl33_99
    | ~ spl33_287 ),
    inference(superposition,[],[f8848,f25580])).

fof(f28789,plain,
    ( ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28788])).

fof(f28788,plain,
    ( $false
    | ~ spl33_10
    | spl33_98
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28787,f2291])).

fof(f28787,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_98
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26970,f25580])).

fof(f26970,plain,
    ( ~ v1_xboole_0(sK22(sK28(k1_xboole_0)))
    | spl33_98
    | ~ spl33_287 ),
    inference(superposition,[],[f8833,f25580])).

fof(f28786,plain,
    ( ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28785])).

fof(f28785,plain,
    ( $false
    | ~ spl33_10
    | spl33_42
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28784,f2291])).

fof(f28784,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_42
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26969,f25580])).

fof(f26969,plain,
    ( ~ v1_xboole_0(sK27(k1_xboole_0))
    | spl33_42
    | ~ spl33_287 ),
    inference(superposition,[],[f3096,f25580])).

fof(f28783,plain,
    ( ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28782])).

fof(f28782,plain,
    ( $false
    | ~ spl33_10
    | spl33_41
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28781,f2291])).

fof(f28781,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_41
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26968,f25580])).

fof(f26968,plain,
    ( ~ v1_xboole_0(sK22(k1_xboole_0))
    | spl33_41
    | ~ spl33_287 ),
    inference(superposition,[],[f3091,f25580])).

fof(f28780,plain,
    ( ~ spl33_10
    | spl33_40
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28779])).

fof(f28779,plain,
    ( $false
    | ~ spl33_10
    | spl33_40
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26967,f2291])).

fof(f26967,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_40
    | ~ spl33_287 ),
    inference(superposition,[],[f3086,f25580])).

fof(f28778,plain,
    ( ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28777])).

fof(f28777,plain,
    ( $false
    | ~ spl33_10
    | spl33_39
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28776,f2291])).

fof(f28776,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_39
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26966,f25580])).

fof(f26966,plain,
    ( ~ v1_xboole_0(sK15(k1_xboole_0))
    | spl33_39
    | ~ spl33_287 ),
    inference(superposition,[],[f3082,f25580])).

fof(f28775,plain,
    ( ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28774])).

fof(f28774,plain,
    ( $false
    | ~ spl33_10
    | spl33_37
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28773,f2291])).

fof(f28773,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_37
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26965,f25580])).

fof(f26965,plain,
    ( ~ v1_xboole_0(sK3(k1_xboole_0))
    | spl33_37
    | ~ spl33_287 ),
    inference(superposition,[],[f3073,f25580])).

fof(f28772,plain,
    ( ~ spl33_10
    | spl33_35
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28771])).

fof(f28771,plain,
    ( $false
    | ~ spl33_10
    | spl33_35
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26962,f2291])).

fof(f26962,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_35
    | ~ spl33_287 ),
    inference(superposition,[],[f3065,f25580])).

fof(f28333,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28332])).

fof(f28332,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26385,f2079])).

fof(f26385,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3633,f25580])).

fof(f3633,plain,(
    ! [X1] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_zfmisc_1(X1))),X1) ),
    inference(resolution,[],[f3624,f2226])).

fof(f2226,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f2012])).

fof(f2012,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1917])).

fof(f1917,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f1915,f1916])).

fof(f1916,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1915,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f1914])).

fof(f1914,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f3624,plain,(
    ! [X0] : ~ r2_hidden(k1_zfmisc_1(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f3586,f2174])).

fof(f2174,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1986])).

fof(f1986,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f395])).

fof(f395,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f3586,plain,(
    ! [X1] : ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_zfmisc_1(X1))),X1) ),
    inference(resolution,[],[f3577,f2226])).

fof(f3577,plain,(
    ! [X0] : ~ r2_hidden(k1_tarski(k1_zfmisc_1(X0)),X0) ),
    inference(resolution,[],[f3557,f2174])).

fof(f3557,plain,(
    ! [X1] : ~ r1_tarski(k1_tarski(k1_tarski(k1_zfmisc_1(X1))),X1) ),
    inference(resolution,[],[f3552,f2226])).

fof(f3552,plain,(
    ! [X1] : ~ r2_hidden(k1_tarski(k1_tarski(X1)),X1) ),
    inference(resolution,[],[f2833,f2237])).

fof(f2237,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f2236])).

fof(f2236,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f2178])).

fof(f2178,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1991])).

fof(f1991,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK29(X0,X1) != X0
            | ~ r2_hidden(sK29(X0,X1),X1) )
          & ( sK29(X0,X1) = X0
            | r2_hidden(sK29(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK29])],[f1989,f1990])).

fof(f1990,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK29(X0,X1) != X0
          | ~ r2_hidden(sK29(X0,X1),X1) )
        & ( sK29(X0,X1) = X0
          | r2_hidden(sK29(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1989,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f1988])).

fof(f1988,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f2833,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_tarski(X1),X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f2006,f2237])).

fof(f2006,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1775])).

fof(f1775,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1111])).

fof(f1111,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X2,X0)
        & r2_hidden(X1,X2)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_ordinal1)).

fof(f28331,plain,
    ( spl33_52
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28330])).

fof(f28330,plain,
    ( $false
    | spl33_52
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26384,f2079])).

fof(f26384,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_52
    | ~ spl33_287 ),
    inference(superposition,[],[f3643,f25580])).

fof(f3643,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | spl33_52 ),
    inference(avatar_component_clause,[],[f3641])).

fof(f3641,plain,
    ( spl33_52
  <=> r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_52])])).

fof(f28328,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28327])).

fof(f28327,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28326,f2079])).

fof(f28326,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f28325,f25580])).

fof(f28325,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26379,f2261])).

fof(f2261,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)
    | ~ spl33_4 ),
    inference(avatar_component_clause,[],[f2259])).

fof(f2259,plain,
    ( spl33_4
  <=> k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_4])])).

fof(f26379,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3633,f25580])).

fof(f28322,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28321])).

fof(f28321,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28320,f2079])).

fof(f28320,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26375,f25580])).

fof(f26375,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3586,f25580])).

fof(f28309,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28308])).

fof(f28308,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26365,f2367])).

fof(f2367,plain,(
    ! [X0] : ~ r2_hidden(k1_tarski(X0),X0) ),
    inference(resolution,[],[f2035,f2237])).

fof(f2035,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1794])).

fof(f1794,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f26365,plain,
    ( r2_hidden(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2767,f25580])).

fof(f2767,plain,(
    ! [X11] : r2_hidden(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X11))) ),
    inference(subsumption_resolution,[],[f2760,f2160])).

fof(f2760,plain,(
    ! [X11] :
      ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(X11)))
      | r2_hidden(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X11))) ) ),
    inference(resolution,[],[f2132,f2077])).

fof(f2077,plain,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(cnf_transformation,[],[f631])).

fof(f631,axiom,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).

fof(f28307,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28306])).

fof(f28306,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26364,f2079])).

fof(f26364,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2577,f25580])).

fof(f2577,plain,(
    ! [X8] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(X8)),X8) ),
    inference(resolution,[],[f2226,f2549])).

fof(f2549,plain,(
    ! [X0] : ~ r2_hidden(k1_zfmisc_1(X0),X0) ),
    inference(resolution,[],[f2547,f2035])).

fof(f2547,plain,(
    ! [X4] : r2_hidden(X4,k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f2173,f2200])).

fof(f2173,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1986])).

fof(f28303,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28302])).

fof(f28302,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26361,f2079])).

fof(f26361,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3574,f25580])).

fof(f3574,plain,(
    ! [X1] : ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_zfmisc_1(X1))),X1) ),
    inference(resolution,[],[f3553,f2226])).

fof(f3553,plain,(
    ! [X2] : ~ r2_hidden(k1_zfmisc_1(k1_tarski(X2)),X2) ),
    inference(resolution,[],[f2833,f2547])).

fof(f28301,plain,
    ( spl33_50
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28300])).

fof(f28300,plain,
    ( $false
    | spl33_50
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26360,f2079])).

fof(f26360,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_50
    | ~ spl33_287 ),
    inference(superposition,[],[f3608,f25580])).

fof(f3608,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | spl33_50 ),
    inference(avatar_component_clause,[],[f3606])).

fof(f3606,plain,
    ( spl33_50
  <=> r1_tarski(k1_zfmisc_1(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_50])])).

fof(f28293,plain,
    ( spl33_32
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28292])).

fof(f28292,plain,
    ( $false
    | spl33_32
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26351,f2079])).

fof(f26351,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_32
    | ~ spl33_287 ),
    inference(superposition,[],[f2606,f25580])).

fof(f2606,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | spl33_32 ),
    inference(avatar_component_clause,[],[f2604])).

fof(f2604,plain,
    ( spl33_32
  <=> r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_32])])).

fof(f28252,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28251])).

fof(f28251,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26306,f2355])).

fof(f26306,plain,
    ( r2_hidden(k3_tarski(sK28(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f12170,f25580])).

fof(f28247,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28246])).

fof(f28246,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26302,f2355])).

fof(f26302,plain,
    ( r2_hidden(k3_tarski(sK26(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f12143,f25580])).

fof(f28236,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28235])).

fof(f28235,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26291,f2355])).

fof(f26291,plain,
    ( r2_hidden(k3_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f10628,f25580])).

fof(f10628,plain,(
    ! [X33] : r2_hidden(k3_tarski(k1_zfmisc_1(X33)),k1_zfmisc_1(X33)) ),
    inference(subsumption_resolution,[],[f10624,f2160])).

fof(f10624,plain,(
    ! [X33] :
      ( v1_xboole_0(k1_zfmisc_1(X33))
      | r2_hidden(k3_tarski(k1_zfmisc_1(X33)),k1_zfmisc_1(X33)) ) ),
    inference(resolution,[],[f9830,f2132])).

fof(f9830,plain,(
    ! [X4] : m1_subset_1(k3_tarski(k1_zfmisc_1(X4)),k1_zfmisc_1(X4)) ),
    inference(resolution,[],[f3576,f2550])).

fof(f2550,plain,(
    ! [X1] : m1_subset_1(X1,k1_zfmisc_1(X1)) ),
    inference(resolution,[],[f2547,f2034])).

fof(f2034,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1793])).

fof(f1793,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f591])).

fof(f591,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f28221,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28220])).

fof(f28220,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26267,f2355])).

fof(f26267,plain,
    ( ! [X0] : r2_hidden(sK27(sK28(k1_tarski(X0))),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f9079,f25580])).

fof(f28218,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28217])).

fof(f28217,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26265,f2355])).

fof(f26265,plain,
    ( ! [X0] : r2_hidden(sK22(sK28(k1_tarski(X0))),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f8822,f25580])).

fof(f28190,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28189])).

fof(f28189,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26237,f2079])).

fof(f26237,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(superposition,[],[f6093,f25580])).

fof(f6093,plain,
    ( ! [X20] : ~ r1_tarski(k1_zfmisc_1(X20),k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f2578,f2480])).

fof(f2480,plain,(
    ! [X0] : ~ r2_hidden(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f2465,f2010])).

fof(f2010,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1779])).

fof(f1779,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2465,plain,(
    ! [X5] : r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1(X5)) ),
    inference(resolution,[],[f2106,f2077])).

fof(f2106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1966])).

fof(f1966,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f2578,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2226,f2261])).

fof(f28182,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28181])).

fof(f28181,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28180,f2079])).

fof(f28180,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26212,f25580])).

fof(f26212,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3633,f25580])).

fof(f28176,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28175])).

fof(f28175,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28174,f2079])).

fof(f28174,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26204,f25580])).

fof(f26204,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_xboole_0)),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3586,f25580])).

fof(f28169,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28168])).

fof(f28168,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28167,f2079])).

fof(f28167,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26201,f25580])).

fof(f26201,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3574,f25580])).

fof(f28142,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28141])).

fof(f28141,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28140,f2079])).

fof(f28140,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26192,f25580])).

fof(f26192,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3557,f25580])).

fof(f28135,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28134])).

fof(f28134,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28133,f2079])).

fof(f28133,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f28132,f25580])).

fof(f28132,plain,
    ( ! [X0,X1] : ~ r1_tarski(k1_zfmisc_1(X1),X0)
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26187,f2079])).

fof(f26187,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X1)
        | ~ r1_tarski(k1_zfmisc_1(X1),X0) )
    | ~ spl33_287 ),
    inference(superposition,[],[f3335,f25580])).

fof(f3335,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k1_zfmisc_1(X5),X4)
      | ~ r1_tarski(k1_zfmisc_1(X4),X5) ) ),
    inference(resolution,[],[f2573,f2226])).

fof(f2573,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_zfmisc_1(X2),X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f2226,f2035])).

fof(f28130,plain,
    ( ~ spl33_16
    | ~ spl33_18
    | ~ spl33_43
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28129])).

fof(f28129,plain,
    ( $false
    | ~ spl33_16
    | ~ spl33_18
    | ~ spl33_43
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28128,f2326])).

fof(f2326,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl33_16 ),
    inference(avatar_component_clause,[],[f2324])).

fof(f2324,plain,
    ( spl33_16
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_16])])).

fof(f28128,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl33_18
    | ~ spl33_43
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26184,f2339])).

fof(f2339,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl33_18 ),
    inference(avatar_component_clause,[],[f2337])).

fof(f2337,plain,
    ( spl33_18
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_18])])).

fof(f26184,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl33_43
    | ~ spl33_287 ),
    inference(superposition,[],[f3150,f25580])).

fof(f3150,plain,
    ( ! [X10] :
        ( ~ v1_funct_1(k1_zfmisc_1(X10))
        | ~ v1_relat_1(k1_zfmisc_1(X10)) )
    | ~ spl33_43 ),
    inference(avatar_component_clause,[],[f3149])).

fof(f3149,plain,
    ( spl33_43
  <=> ! [X10] :
        ( ~ v1_funct_1(k1_zfmisc_1(X10))
        | ~ v1_relat_1(k1_zfmisc_1(X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_43])])).

fof(f28108,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28107])).

fof(f28107,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26158,f2355])).

fof(f26158,plain,
    ( ! [X0] : r2_hidden(sK26(X0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2768,f25580])).

fof(f2768,plain,(
    ! [X13] : r2_hidden(sK26(X13),k1_zfmisc_1(X13)) ),
    inference(subsumption_resolution,[],[f2762,f2160])).

fof(f2762,plain,(
    ! [X13] :
      ( v1_xboole_0(k1_zfmisc_1(X13))
      | r2_hidden(sK26(X13),k1_zfmisc_1(X13)) ) ),
    inference(resolution,[],[f2132,f2143])).

fof(f28106,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28105])).

fof(f28105,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28104,f2362])).

fof(f2362,plain,(
    ! [X1] : ~ r2_hidden(X1,X1) ),
    inference(resolution,[],[f2010,f2234])).

fof(f2234,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2117])).

fof(f2117,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1970])).

fof(f1970,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f1969])).

fof(f1969,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f28104,plain,
    ( r2_hidden(k1_tarski(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26157,f2261])).

fof(f26157,plain,
    ( r2_hidden(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl33_287 ),
    inference(superposition,[],[f2767,f25580])).

fof(f28101,plain,
    ( ~ spl33_16
    | ~ spl33_33
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28100])).

fof(f28100,plain,
    ( $false
    | ~ spl33_16
    | ~ spl33_33
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26152,f2326])).

fof(f26152,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl33_33
    | ~ spl33_287 ),
    inference(superposition,[],[f2730,f25580])).

fof(f2730,plain,
    ( ! [X10] : ~ v1_relat_1(k1_zfmisc_1(X10))
    | ~ spl33_33 ),
    inference(avatar_component_clause,[],[f2729])).

fof(f2729,plain,
    ( spl33_33
  <=> ! [X10] : ~ v1_relat_1(k1_zfmisc_1(X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_33])])).

fof(f28096,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28095])).

fof(f28095,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28094,f2079])).

fof(f28094,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f28093,f25580])).

fof(f28093,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26146,f2261])).

fof(f26146,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2577,f25580])).

fof(f28092,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28091])).

fof(f28091,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28090,f2079])).

fof(f28090,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26145,f25580])).

fof(f26145,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2576,f25580])).

fof(f2576,plain,(
    ! [X7] : ~ r1_tarski(k1_tarski(k1_zfmisc_1(X7)),X7) ),
    inference(resolution,[],[f2226,f2367])).

fof(f28089,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28088])).

fof(f28088,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26143,f2079])).

fof(f26143,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2572,f25580])).

fof(f2572,plain,(
    ! [X0] : ~ r1_tarski(k1_zfmisc_1(X0),X0) ),
    inference(resolution,[],[f2226,f2362])).

fof(f28086,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28085])).

fof(f28085,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26139,f2355])).

fof(f26139,plain,
    ( r2_hidden(k1_xboole_0,k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2548,f25580])).

fof(f2548,plain,(
    ! [X5] : r2_hidden(k1_xboole_0,k1_zfmisc_1(X5)) ),
    inference(resolution,[],[f2173,f2465])).

fof(f28084,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28083])).

fof(f28083,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26138,f2355])).

fof(f26138,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2547,f25580])).

fof(f28077,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28076])).

fof(f28076,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26133,f2237])).

fof(f26133,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl33_287 ),
    inference(superposition,[],[f2480,f25580])).

fof(f28073,plain,
    ( spl33_30
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28072])).

fof(f28072,plain,
    ( $false
    | spl33_30
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26130,f2584])).

fof(f2584,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0)
    | spl33_30 ),
    inference(avatar_component_clause,[],[f2582])).

fof(f2582,plain,
    ( spl33_30
  <=> r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_30])])).

fof(f26130,plain,
    ( r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2465,f25580])).

fof(f28060,plain,
    ( ~ spl33_10
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28059])).

fof(f28059,plain,
    ( $false
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26119,f2291])).

fof(f26119,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2160,f25580])).

fof(f28048,plain,
    ( spl33_51
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28047])).

fof(f28047,plain,
    ( $false
    | spl33_51
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26099,f2079])).

fof(f26099,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_51
    | ~ spl33_287 ),
    inference(superposition,[],[f3630,f25580])).

fof(f3630,plain,
    ( ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | spl33_51 ),
    inference(avatar_component_clause,[],[f3628])).

fof(f3628,plain,
    ( spl33_51
  <=> r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_51])])).

fof(f28046,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28045])).

fof(f28045,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26098,f2079])).

fof(f26098,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3586,f25580])).

fof(f28044,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28043])).

fof(f28043,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26097,f2079])).

fof(f26097,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2576,f25580])).

fof(f28042,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28041])).

fof(f28041,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28040,f2079])).

fof(f28040,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26096,f25580])).

fof(f26096,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3557,f25580])).

fof(f28039,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28038])).

fof(f28038,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f28037,f2079])).

fof(f28037,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f28036,f25580])).

fof(f28036,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_xboole_0),X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f26094,f2261])).

fof(f26094,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_xboole_0),X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3574,f25580])).

fof(f28034,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28033])).

fof(f28033,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26092,f2079])).

fof(f26092,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_287 ),
    inference(superposition,[],[f3557,f25580])).

fof(f28032,plain,
    ( spl33_49
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28031])).

fof(f28031,plain,
    ( $false
    | spl33_49
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26091,f2079])).

fof(f26091,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_49
    | ~ spl33_287 ),
    inference(superposition,[],[f3583,f25580])).

fof(f3583,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | spl33_49 ),
    inference(avatar_component_clause,[],[f3581])).

fof(f3581,plain,
    ( spl33_49
  <=> r1_tarski(k1_tarski(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_49])])).

fof(f28030,plain,
    ( spl33_31
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28029])).

fof(f28029,plain,
    ( $false
    | spl33_31
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26090,f2079])).

fof(f26090,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_31
    | ~ spl33_287 ),
    inference(superposition,[],[f2592,f25580])).

fof(f2592,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | spl33_31 ),
    inference(avatar_component_clause,[],[f2590])).

fof(f2590,plain,
    ( spl33_31
  <=> r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_31])])).

fof(f28004,plain,
    ( spl33_101
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f28003])).

fof(f28003,plain,
    ( $false
    | spl33_101
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26040,f25580])).

fof(f26040,plain,
    ( k1_xboole_0 != sK28(k1_xboole_0)
    | spl33_101
    | ~ spl33_287 ),
    inference(superposition,[],[f9475,f25580])).

fof(f9475,plain,
    ( k1_xboole_0 != sK28(k1_tarski(k1_xboole_0))
    | spl33_101 ),
    inference(avatar_component_clause,[],[f9474])).

fof(f9474,plain,
    ( spl33_101
  <=> k1_xboole_0 = sK28(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_101])])).

fof(f27989,plain,
    ( spl33_34
    | ~ spl33_71
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27988])).

fof(f27988,plain,
    ( $false
    | spl33_34
    | ~ spl33_71
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f26023,f2733])).

fof(f2733,plain,
    ( ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | spl33_34 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f2732,plain,
    ( spl33_34
  <=> v1_relat_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_34])])).

fof(f26023,plain,
    ( v1_relat_1(k1_tarski(k1_xboole_0))
    | ~ spl33_71
    | ~ spl33_287 ),
    inference(superposition,[],[f6413,f25580])).

fof(f6413,plain,
    ( v1_relat_1(k1_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl33_71 ),
    inference(avatar_component_clause,[],[f6411])).

fof(f6411,plain,
    ( spl33_71
  <=> v1_relat_1(k1_tarski(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_71])])).

fof(f27971,plain,
    ( ~ spl33_18
    | spl33_44
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27970])).

fof(f27970,plain,
    ( $false
    | ~ spl33_18
    | spl33_44
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25997,f2339])).

fof(f25997,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl33_44
    | ~ spl33_287 ),
    inference(superposition,[],[f3153,f25580])).

fof(f3153,plain,
    ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
    | spl33_44 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3152,plain,
    ( spl33_44
  <=> v1_funct_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_44])])).

fof(f27968,plain,
    ( ~ spl33_16
    | spl33_34
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27967])).

fof(f27967,plain,
    ( $false
    | ~ spl33_16
    | spl33_34
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25989,f2326])).

fof(f25989,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl33_34
    | ~ spl33_287 ),
    inference(superposition,[],[f2733,f25580])).

fof(f27965,plain,
    ( spl33_30
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27964])).

fof(f27964,plain,
    ( $false
    | spl33_30
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25983,f2079])).

fof(f25983,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl33_30
    | ~ spl33_287 ),
    inference(superposition,[],[f2584,f25580])).

fof(f27947,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27946])).

fof(f27946,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27945,f2355])).

fof(f27945,plain,
    ( r2_hidden(sK27(sK28(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25950,f25580])).

fof(f25950,plain,
    ( ! [X0] : r2_hidden(sK27(sK28(k1_xboole_0)),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f9079,f25580])).

fof(f27935,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27934])).

fof(f27934,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27933,f2355])).

fof(f27933,plain,
    ( r2_hidden(sK22(sK28(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25943,f25580])).

fof(f25943,plain,
    ( ! [X0] : r2_hidden(sK22(sK28(k1_xboole_0)),k1_zfmisc_1(X0))
    | ~ spl33_287 ),
    inference(superposition,[],[f8822,f25580])).

fof(f27899,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27898])).

fof(f27898,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25863,f2355])).

fof(f25863,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2237,f25580])).

fof(f27897,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27896])).

fof(f27896,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25859,f25580])).

fof(f25859,plain,
    ( ! [X1] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X1)
    | ~ spl33_287 ),
    inference(superposition,[],[f2195,f25580])).

fof(f2195,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f407])).

fof(f407,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f27881,plain,
    ( ~ spl33_10
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27880])).

fof(f27880,plain,
    ( $false
    | ~ spl33_10
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f25842,f2291])).

fof(f25842,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_287 ),
    inference(superposition,[],[f2161,f25580])).

fof(f27829,plain,
    ( ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27828])).

fof(f27828,plain,
    ( $false
    | ~ spl33_10
    | spl33_278
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27827,f2291])).

fof(f27827,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl33_278
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25778,f25580])).

fof(f25778,plain,
    ( ! [X0] : ~ v1_xboole_0(sK6(u1_pre_topc(sK2),X0))
    | spl33_278
    | ~ spl33_287 ),
    inference(superposition,[],[f24059,f25580])).

fof(f27720,plain,
    ( ~ spl33_4
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27719])).

fof(f27719,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27718,f2079])).

fof(f27718,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25676,f25580])).

fof(f25676,plain,
    ( ! [X0,X1] : ~ r1_tarski(k1_zfmisc_1(X1),X0)
    | ~ spl33_4
    | ~ spl33_287 ),
    inference(superposition,[],[f6093,f25580])).

fof(f27687,plain,
    ( spl33_52
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27686])).

fof(f27686,plain,
    ( $false
    | spl33_52
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27685,f2079])).

fof(f27685,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_52
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25654,f25580])).

fof(f25654,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_tarski(X0))),X0)
    | spl33_52
    | ~ spl33_287 ),
    inference(superposition,[],[f3643,f25580])).

fof(f27684,plain,
    ( spl33_51
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27683])).

fof(f27683,plain,
    ( $false
    | spl33_51
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27682,f2079])).

fof(f27682,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_51
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25653,f25580])).

fof(f25653,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(X0))),X0)
    | spl33_51
    | ~ spl33_287 ),
    inference(superposition,[],[f3630,f25580])).

fof(f27681,plain,
    ( spl33_50
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27680])).

fof(f27680,plain,
    ( $false
    | spl33_50
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27679,f2079])).

fof(f27679,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_50
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25652,f25580])).

fof(f25652,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_tarski(X0))),X0)
    | spl33_50
    | ~ spl33_287 ),
    inference(superposition,[],[f3608,f25580])).

fof(f27678,plain,
    ( spl33_49
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27677])).

fof(f27677,plain,
    ( $false
    | spl33_49
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27676,f2079])).

fof(f27676,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_49
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25651,f25580])).

fof(f25651,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_tarski(k1_tarski(X0))),X0)
    | spl33_49
    | ~ spl33_287 ),
    inference(superposition,[],[f3583,f25580])).

fof(f27661,plain,
    ( ~ spl33_18
    | spl33_44
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27660])).

fof(f27660,plain,
    ( $false
    | ~ spl33_18
    | spl33_44
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27659,f2339])).

fof(f27659,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl33_44
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25639,f25580])).

fof(f25639,plain,
    ( ! [X0] : ~ v1_funct_1(k1_tarski(X0))
    | spl33_44
    | ~ spl33_287 ),
    inference(superposition,[],[f3153,f25580])).

fof(f27653,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27652])).

fof(f27652,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27651,f2355])).

fof(f27651,plain,
    ( ! [X0] : r2_hidden(k1_tarski(X0),k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25631,f25580])).

fof(f25631,plain,
    ( ! [X0,X1] : r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
    | ~ spl33_287 ),
    inference(superposition,[],[f2767,f25580])).

fof(f27648,plain,
    ( ~ spl33_16
    | spl33_34
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27647])).

fof(f27647,plain,
    ( $false
    | ~ spl33_16
    | spl33_34
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27646,f2326])).

fof(f27646,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl33_34
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25629,f25580])).

fof(f25629,plain,
    ( ! [X0] : ~ v1_relat_1(k1_tarski(X0))
    | spl33_34
    | ~ spl33_287 ),
    inference(superposition,[],[f2733,f25580])).

fof(f27642,plain,
    ( spl33_32
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27641])).

fof(f27641,plain,
    ( $false
    | spl33_32
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27640,f2079])).

fof(f27640,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_32
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25626,f25580])).

fof(f25626,plain,
    ( ! [X0] : ~ r1_tarski(k1_zfmisc_1(k1_tarski(X0)),X0)
    | spl33_32
    | ~ spl33_287 ),
    inference(superposition,[],[f2606,f25580])).

fof(f27638,plain,
    ( spl33_31
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27637])).

fof(f27637,plain,
    ( $false
    | spl33_31
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27636,f2079])).

fof(f27636,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_31
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25624,f25580])).

fof(f25624,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(k1_tarski(X0)),X0)
    | spl33_31
    | ~ spl33_287 ),
    inference(superposition,[],[f2592,f25580])).

fof(f27635,plain,
    ( spl33_30
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27634])).

fof(f27634,plain,
    ( $false
    | spl33_30
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27633,f2079])).

fof(f27633,plain,
    ( ! [X0] : ~ r1_tarski(k1_xboole_0,X0)
    | spl33_30
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25623,f25580])).

fof(f25623,plain,
    ( ! [X0] : ~ r1_tarski(k1_tarski(X0),X0)
    | spl33_30
    | ~ spl33_287 ),
    inference(superposition,[],[f2584,f25580])).

fof(f27630,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27629])).

fof(f27629,plain,
    ( $false
    | ~ spl33_287 ),
    inference(subsumption_resolution,[],[f27628,f2355])).

fof(f27628,plain,
    ( ! [X0] : r2_hidden(X0,k1_xboole_0)
    | ~ spl33_287 ),
    inference(forward_demodulation,[],[f25621,f25580])).

fof(f25621,plain,
    ( ! [X0,X1] : r2_hidden(X0,k1_zfmisc_1(X1))
    | ~ spl33_287 ),
    inference(superposition,[],[f2548,f25580])).

fof(f27609,plain,(
    ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27608])).

fof(f27608,plain,
    ( $false
    | ~ spl33_287 ),
    inference(trivial_inequality_removal,[],[f25800])).

fof(f25800,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl33_287 ),
    inference(superposition,[],[f2195,f25580])).

fof(f27600,plain,
    ( spl33_47
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27599])).

fof(f27599,plain,
    ( $false
    | spl33_47
    | ~ spl33_287 ),
    inference(trivial_inequality_removal,[],[f26001])).

fof(f26001,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl33_47
    | ~ spl33_287 ),
    inference(superposition,[],[f3402,f25580])).

fof(f3402,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | spl33_47 ),
    inference(avatar_component_clause,[],[f3401])).

fof(f3401,plain,
    ( spl33_47
  <=> k1_xboole_0 = k1_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_47])])).

fof(f27590,plain,
    ( spl33_101
    | ~ spl33_287 ),
    inference(avatar_contradiction_clause,[],[f27589])).

fof(f27589,plain,
    ( $false
    | spl33_101
    | ~ spl33_287 ),
    inference(trivial_inequality_removal,[],[f27523])).

fof(f27523,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl33_101
    | ~ spl33_287 ),
    inference(superposition,[],[f9475,f25580])).

fof(f25581,plain,
    ( spl33_286
    | spl33_287 ),
    inference(avatar_split_clause,[],[f25453,f25579,f25576])).

fof(f25576,plain,
    ( spl33_286
  <=> ! [X470] : ~ r1_tarski(k1_tarski(X470),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_286])])).

fof(f25453,plain,(
    ! [X471,X470] :
      ( k1_xboole_0 = X471
      | ~ r1_tarski(k1_tarski(X470),k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f25443])).

fof(f25443,plain,(
    ! [X471,X470] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = X471
      | ~ r1_tarski(k1_tarski(X470),k1_xboole_0) ) ),
    inference(superposition,[],[f2063,f7004])).

fof(f7004,plain,(
    ! [X8,X7] :
      ( k1_xboole_0 = k2_zfmisc_1(X7,X8)
      | ~ r1_tarski(X7,k1_xboole_0) ) ),
    inference(resolution,[],[f3168,f2075])).

fof(f2075,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1816])).

fof(f1816,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f101])).

fof(f101,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f3168,plain,(
    ! [X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X2),k1_xboole_0)
      | ~ r1_tarski(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f2114,f2229])).

fof(f2229,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2049])).

fof(f2049,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1944])).

fof(f2114,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1834])).

fof(f1834,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f334])).

fof(f334,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f2063,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1811])).

fof(f1811,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f347])).

fof(f347,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f24187,plain,
    ( spl33_280
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24186,f24052,f2289,f24144])).

fof(f24144,plain,
    ( spl33_280
  <=> v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_280])])).

fof(f24052,plain,
    ( spl33_277
  <=> r1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_277])])).

fof(f24186,plain,
    ( v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24134,f2291])).

fof(f24134,plain,
    ( v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f3352])).

fof(f3352,plain,(
    ! [X4,X2] :
      ( ~ r1_tarski(X4,X2)
      | v1_relat_1(X4)
      | ~ v1_xboole_0(X2) ) ),
    inference(superposition,[],[f2689,f2357])).

fof(f2357,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2229,f2152])).

fof(f2689,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f2105,f2107])).

fof(f2107,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1966])).

fof(f2105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1825])).

fof(f1825,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f24054,plain,
    ( r1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl33_277 ),
    inference(avatar_component_clause,[],[f24052])).

fof(f24185,plain,
    ( spl33_279
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24184,f24052,f2289,f24139])).

fof(f24139,plain,
    ( spl33_279
  <=> k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_279])])).

fof(f24184,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24133,f2291])).

fof(f24133,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f3182])).

fof(f3182,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k1_xboole_0 = X2
      | ~ v1_xboole_0(X3) ) ),
    inference(superposition,[],[f2057,f2354])).

fof(f2354,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2228,f2152])).

fof(f2057,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1804])).

fof(f1804,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
        & ~ r1_tarski(X0,k2_zfmisc_1(X0,X1)) ) ) ),
    inference(ennf_transformation,[],[f351])).

fof(f351,axiom,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k2_zfmisc_1(X1,X0))
        | r1_tarski(X0,k2_zfmisc_1(X0,X1)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

fof(f24183,plain,
    ( spl33_285
    | ~ spl33_16
    | ~ spl33_18
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24178,f24052,f2337,f2324,f24180])).

fof(f24180,plain,
    ( spl33_285
  <=> v1_funct_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_285])])).

fof(f24178,plain,
    ( v1_funct_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_16
    | ~ spl33_18
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24177,f2326])).

fof(f24177,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_funct_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_18
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24132,f2339])).

fof(f24132,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | v1_funct_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f3134])).

fof(f3134,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | v1_funct_1(X0) ) ),
    inference(resolution,[],[f2109,f2107])).

fof(f2109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1827])).

fof(f1827,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1826])).

fof(f1826,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f892])).

fof(f892,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_funct_1)).

fof(f24176,plain,
    ( spl33_281
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24175,f24052,f2289,f24149])).

fof(f24149,plain,
    ( spl33_281
  <=> v1_xboole_0(sK6(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_281])])).

fof(f24175,plain,
    ( v1_xboole_0(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24128,f2291])).

fof(f24128,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2782])).

fof(f2782,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2149,f2107])).

fof(f2149,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1856])).

fof(f1856,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f541])).

fof(f541,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f24174,plain,
    ( spl33_280
    | ~ spl33_16
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24173,f24052,f2324,f24144])).

fof(f24173,plain,
    ( v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_16
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24127,f2326])).

fof(f24127,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2716])).

fof(f2716,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f2110,f2107])).

fof(f2110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1828])).

fof(f1828,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f24172,plain,
    ( spl33_279
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24171,f24052,f2289,f24139])).

fof(f24171,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24126,f2291])).

fof(f24126,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2375])).

fof(f2375,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2075,f2152])).

fof(f24170,plain,
    ( spl33_279
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24169,f24052,f24139])).

fof(f24169,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_277 ),
    inference(subsumption_resolution,[],[f24125,f2079])).

fof(f24125,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2118])).

fof(f2118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1970])).

fof(f24167,plain,
    ( ~ spl33_284
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24122,f24052,f24164])).

fof(f24164,plain,
    ( spl33_284
  <=> r2_hidden(k1_xboole_0,sK6(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_284])])).

fof(f24122,plain,
    ( ~ r2_hidden(k1_xboole_0,sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2010])).

fof(f24162,plain,
    ( spl33_283
    | ~ spl33_221
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24121,f24052,f14348,f24159])).

fof(f24159,plain,
    ( spl33_283
  <=> v1_funct_1(k1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_283])])).

fof(f14348,plain,
    ( spl33_221
  <=> ! [X1] :
        ( v1_funct_1(k1_tarski(X1))
        | ~ r1_tarski(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_221])])).

fof(f24121,plain,
    ( v1_funct_1(k1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0)))
    | ~ spl33_221
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f14349])).

fof(f14349,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | v1_funct_1(k1_tarski(X1)) )
    | ~ spl33_221 ),
    inference(avatar_component_clause,[],[f14348])).

fof(f24157,plain,
    ( spl33_282
    | ~ spl33_4
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24120,f24052,f2259,f24154])).

fof(f24154,plain,
    ( spl33_282
  <=> v1_relat_1(k1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_282])])).

fof(f24120,plain,
    ( v1_relat_1(k1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f7349])).

fof(f7349,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_relat_1(k1_relat_1(X0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3505,f2479])).

fof(f2479,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2107,f2261])).

fof(f3505,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_tarski(k1_xboole_0))
        | v1_relat_1(k1_relat_1(X1)) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f3504,f2261])).

fof(f3504,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(k1_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f3494,f2229])).

fof(f3494,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
      | v1_relat_1(k1_relat_1(X1)) ) ),
    inference(superposition,[],[f2201,f2228])).

fof(f2201,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)))
      | v1_relat_1(k1_relat_1(X3)) ) ),
    inference(cnf_transformation,[],[f1885])).

fof(f1885,plain,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(k1_relat_1(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))) ) ),
    inference(ennf_transformation,[],[f1225])).

fof(f1225,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)))
     => v1_relat_1(k1_relat_1(X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relset_1)).

fof(f24152,plain,
    ( spl33_281
    | ~ spl33_4
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24119,f24052,f2289,f2259,f24149])).

fof(f24119,plain,
    ( v1_xboole_0(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_10
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f6277])).

fof(f6277,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | v1_xboole_0(X0) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f2795,f2479])).

fof(f2795,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f2793,f2291])).

fof(f2793,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_xboole_0(X0)
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2149,f2261])).

fof(f24147,plain,
    ( spl33_280
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24118,f24052,f24144])).

fof(f24118,plain,
    ( v1_relat_1(sK6(k1_tarski(k1_xboole_0),k1_xboole_0))
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f3351])).

fof(f3351,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | v1_relat_1(X1) ) ),
    inference(superposition,[],[f2689,f2228])).

fof(f24142,plain,
    ( spl33_279
    | ~ spl33_277 ),
    inference(avatar_split_clause,[],[f24116,f24052,f24139])).

fof(f24116,plain,
    ( k1_xboole_0 = sK6(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_277 ),
    inference(resolution,[],[f24054,f2075])).

fof(f24060,plain,
    ( ~ spl33_278
    | spl33_38
    | spl33_1 ),
    inference(avatar_split_clause,[],[f24012,f2244,f3076,f24057])).

fof(f3076,plain,
    ( spl33_38
  <=> k1_xboole_0 = u1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_38])])).

fof(f24012,plain,
    ( k1_xboole_0 = u1_pre_topc(sK2)
    | ~ v1_xboole_0(sK6(u1_pre_topc(sK2),k1_xboole_0))
    | spl33_1 ),
    inference(resolution,[],[f3890,f2350])).

fof(f3890,plain,(
    ! [X13] :
      ( r2_hidden(sK6(X13,k1_xboole_0),X13)
      | k1_xboole_0 = X13 ) ),
    inference(resolution,[],[f2018,f2355])).

fof(f2018,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X1)
      | X0 = X1
      | r2_hidden(sK6(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f1924])).

fof(f1924,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1922,f1923])).

fof(f1923,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) )
     => ( ( ~ r2_hidden(sK6(X0,X1),X1)
          | ~ r2_hidden(sK6(X0,X1),X0) )
        & ( r2_hidden(sK6(X0,X1),X1)
          | r2_hidden(sK6(X0,X1),X0) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f1922,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
          & ( r2_hidden(X2,X1)
            | r2_hidden(X2,X0) ) ) ) ),
    inference(nnf_transformation,[],[f1781])).

fof(f1781,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

fof(f24055,plain,
    ( spl33_277
    | ~ spl33_4
    | spl33_47 ),
    inference(avatar_split_clause,[],[f24050,f3401,f2259,f24052])).

fof(f24050,plain,
    ( r1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f23989,f3402])).

fof(f23989,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | r1_tarski(sK6(k1_tarski(k1_xboole_0),k1_xboole_0),k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f3890,f2600])).

fof(f2600,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tarski(k1_xboole_0))
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2227,f2261])).

fof(f2227,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f2011])).

fof(f2011,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1917])).

fof(f22312,plain,
    ( ~ spl33_34
    | spl33_221
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(avatar_split_clause,[],[f22311,f3401,f3152,f2259,f14348,f2732])).

fof(f22311,plain,
    ( ! [X3] :
        ( v1_funct_1(k1_tarski(X3))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(subsumption_resolution,[],[f22310,f3154])).

fof(f3154,plain,
    ( v1_funct_1(k1_tarski(k1_xboole_0))
    | ~ spl33_44 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f22310,plain,
    ( ! [X3] :
        ( v1_funct_1(k1_tarski(X3))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14713,f3402])).

fof(f14713,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(k1_tarski(X3))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3431,f2479])).

fof(f3431,plain,(
    ! [X8,X9] :
      ( ~ m1_subset_1(X9,X8)
      | k1_xboole_0 = X8
      | v1_funct_1(k1_tarski(X9))
      | ~ v1_funct_1(X8)
      | ~ v1_relat_1(X8) ) ),
    inference(resolution,[],[f2062,f2109])).

fof(f2062,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f1810])).

fof(f1810,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(flattening,[],[f1809])).

fof(f1809,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X1,X0) ) ),
    inference(ennf_transformation,[],[f527])).

fof(f527,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
     => ( k1_xboole_0 != X0
       => m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_subset_1)).

fof(f22309,plain,
    ( spl33_221
    | spl33_276 ),
    inference(avatar_split_clause,[],[f14718,f22307,f14348])).

fof(f22307,plain,
    ( spl33_276
  <=> ! [X11,X10] :
        ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
        | ~ v1_funct_1(k1_zfmisc_1(k2_zfmisc_1(X10,X11))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_276])])).

fof(f14718,plain,(
    ! [X12,X10,X11] :
      ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
      | v1_funct_1(k1_tarski(X12))
      | ~ v1_funct_1(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(X12,k1_xboole_0) ) ),
    inference(resolution,[],[f3431,f4685])).

fof(f4685,plain,(
    ! [X17,X15,X16] :
      ( m1_subset_1(X15,k1_zfmisc_1(k2_zfmisc_1(X16,X17)))
      | ~ r1_tarski(X15,k1_xboole_0) ) ),
    inference(resolution,[],[f2104,f2065])).

fof(f2065,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1248])).

fof(f1248,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f2104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f1824])).

fof(f1824,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f1823])).

fof(f1823,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1263])).

fof(f1263,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f22305,plain,
    ( ~ spl33_34
    | spl33_216
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(avatar_split_clause,[],[f22304,f3401,f3152,f2259,f14322,f2732])).

fof(f14322,plain,
    ( spl33_216
  <=> ! [X5] :
        ( v1_funct_1(k1_tarski(X5))
        | ~ v1_xboole_0(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_216])])).

fof(f22304,plain,
    ( ! [X4] :
        ( v1_funct_1(k1_tarski(X4))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X4) )
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(subsumption_resolution,[],[f22303,f3154])).

fof(f22303,plain,
    ( ! [X4] :
        ( v1_funct_1(k1_tarski(X4))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X4) )
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14714,f3402])).

fof(f14714,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(k1_tarski(X4))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X4) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3431,f2450])).

fof(f2450,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2347,f2261])).

fof(f2347,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2078,f2152])).

fof(f22302,plain,
    ( spl33_43
    | spl33_216 ),
    inference(avatar_split_clause,[],[f22301,f14322,f3149])).

fof(f22301,plain,(
    ! [X8,X9] :
      ( v1_funct_1(k1_tarski(X9))
      | ~ v1_funct_1(k1_zfmisc_1(X8))
      | ~ v1_relat_1(k1_zfmisc_1(X8))
      | ~ v1_xboole_0(X9) ) ),
    inference(global_subsumption,[],[f5480])).

fof(f5480,plain,(
    ! [X8,X9] :
      ( ~ v1_xboole_0(X8)
      | v1_funct_1(k1_tarski(X8))
      | ~ v1_funct_1(k1_zfmisc_1(X9))
      | ~ v1_relat_1(k1_zfmisc_1(X9)) ) ),
    inference(resolution,[],[f2376,f2109])).

fof(f2376,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2077,f2152])).

fof(f22300,plain,
    ( spl33_43
    | spl33_209 ),
    inference(avatar_split_clause,[],[f22299,f14285,f3149])).

fof(f14285,plain,
    ( spl33_209
  <=> ! [X31] :
        ( ~ v1_xboole_0(X31)
        | v1_funct_1(k1_tarski(k3_tarski(X31))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_209])])).

fof(f22299,plain,(
    ! [X35,X34] :
      ( v1_funct_1(k1_tarski(k3_tarski(X35)))
      | ~ v1_funct_1(k1_zfmisc_1(X34))
      | ~ v1_relat_1(k1_zfmisc_1(X34))
      | ~ v1_xboole_0(X35) ) ),
    inference(global_subsumption,[],[f12781])).

fof(f12781,plain,(
    ! [X31,X32] :
      ( ~ v1_xboole_0(X31)
      | ~ v1_funct_1(k1_zfmisc_1(X32))
      | ~ v1_relat_1(k1_zfmisc_1(X32))
      | v1_funct_1(k1_tarski(k3_tarski(X31))) ) ),
    inference(resolution,[],[f12090,f3141])).

fof(f3141,plain,(
    ! [X12,X11] :
      ( ~ r2_hidden(X11,X12)
      | ~ v1_funct_1(X12)
      | ~ v1_relat_1(X12)
      | v1_funct_1(k1_tarski(X11)) ) ),
    inference(resolution,[],[f2109,f2194])).

fof(f2194,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1883])).

fof(f1883,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f535])).

fof(f535,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f12090,plain,(
    ! [X48,X49] :
      ( r2_hidden(k3_tarski(X48),k1_zfmisc_1(X49))
      | ~ v1_xboole_0(X48) ) ),
    inference(subsumption_resolution,[],[f12081,f2160])).

fof(f12081,plain,(
    ! [X48,X49] :
      ( ~ v1_xboole_0(X48)
      | v1_xboole_0(k1_zfmisc_1(X49))
      | r2_hidden(k3_tarski(X48),k1_zfmisc_1(X49)) ) ),
    inference(resolution,[],[f9829,f2132])).

fof(f9829,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k3_tarski(X2),k1_zfmisc_1(X3))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f3576,f2347])).

fof(f22298,plain,
    ( ~ spl33_34
    | spl33_275
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(avatar_split_clause,[],[f14776,f3401,f3152,f2259,f22296,f2732])).

fof(f22296,plain,
    ( spl33_275
  <=> ! [X49,X48] :
        ( v1_funct_1(k1_tarski(k9_subset_1(k1_xboole_0,X48,X49)))
        | ~ m1_subset_1(X49,k1_tarski(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_275])])).

fof(f14776,plain,
    ( ! [X48,X49] :
        ( v1_funct_1(k1_tarski(k9_subset_1(k1_xboole_0,X48,X49)))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X49,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14775,f3154])).

fof(f14775,plain,
    ( ! [X48,X49] :
        ( v1_funct_1(k1_tarski(k9_subset_1(k1_xboole_0,X48,X49)))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X49,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14738,f3402])).

fof(f14738,plain,
    ( ! [X48,X49] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(k1_tarski(k9_subset_1(k1_xboole_0,X48,X49)))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X49,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3431,f3549])).

fof(f3549,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k9_subset_1(k1_xboole_0,X0,X1),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2213,f2261])).

fof(f2213,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1894])).

fof(f1894,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f472])).

fof(f472,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f22294,plain,
    ( ~ spl33_34
    | spl33_274
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(avatar_split_clause,[],[f14779,f3401,f3152,f2259,f22292,f2732])).

fof(f22292,plain,
    ( spl33_274
  <=> ! [X52] :
        ( v1_funct_1(k1_tarski(k5_setfam_1(k1_xboole_0,X52)))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_274])])).

fof(f14779,plain,
    ( ! [X52] :
        ( v1_funct_1(k1_tarski(k5_setfam_1(k1_xboole_0,X52)))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k1_tarski(k1_xboole_0))) )
    | ~ spl33_4
    | ~ spl33_44
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14778,f3154])).

fof(f14778,plain,
    ( ! [X52] :
        ( v1_funct_1(k1_tarski(k5_setfam_1(k1_xboole_0,X52)))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k1_tarski(k1_xboole_0))) )
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f14740,f3402])).

fof(f14740,plain,
    ( ! [X52] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(k1_tarski(k5_setfam_1(k1_xboole_0,X52)))
        | ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X52,k1_zfmisc_1(k1_tarski(k1_xboole_0))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3431,f3571])).

fof(f3571,plain,
    ( ! [X0] :
        ( m1_subset_1(k5_setfam_1(k1_xboole_0,X0),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tarski(k1_xboole_0))) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2221,f2261])).

fof(f22287,plain,
    ( spl33_273
    | spl33_43 ),
    inference(avatar_split_clause,[],[f22268,f3149,f22284])).

fof(f22284,plain,
    ( spl33_273
  <=> v1_funct_1(k5_setfam_1(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_273])])).

fof(f22268,plain,(
    ! [X17] :
      ( ~ v1_funct_1(k1_zfmisc_1(X17))
      | ~ v1_relat_1(k1_zfmisc_1(X17))
      | v1_funct_1(k5_setfam_1(k1_tarski(k1_xboole_0),k1_xboole_0)) ) ),
    inference(resolution,[],[f22089,f3134])).

fof(f22089,plain,(
    ! [X23] : r1_tarski(k5_setfam_1(k1_tarski(k1_xboole_0),k1_xboole_0),k1_zfmisc_1(X23)) ),
    inference(resolution,[],[f2911,f9664])).

fof(f9664,plain,(
    ! [X7] : r1_tarski(k5_setfam_1(X7,k1_xboole_0),X7) ),
    inference(resolution,[],[f3560,f2078])).

fof(f3560,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X7)))
      | r1_tarski(k5_setfam_1(X7,X6),X7) ) ),
    inference(resolution,[],[f2221,f2106])).

fof(f2911,plain,(
    ! [X35,X34] :
      ( ~ r1_tarski(X34,k1_tarski(k1_xboole_0))
      | r1_tarski(X34,k1_zfmisc_1(X35)) ) ),
    inference(resolution,[],[f2113,f2465])).

fof(f2113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1833])).

fof(f1833,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1832])).

fof(f1832,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f22282,plain,
    ( spl33_272
    | spl33_33 ),
    inference(avatar_split_clause,[],[f22263,f2729,f22279])).

fof(f22279,plain,
    ( spl33_272
  <=> v1_relat_1(k5_setfam_1(k1_tarski(k1_xboole_0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_272])])).

fof(f22263,plain,(
    ! [X9] :
      ( ~ v1_relat_1(k1_zfmisc_1(X9))
      | v1_relat_1(k5_setfam_1(k1_tarski(k1_xboole_0),k1_xboole_0)) ) ),
    inference(resolution,[],[f22089,f2716])).

fof(f22189,plain,
    ( spl33_267
    | spl33_271 ),
    inference(avatar_split_clause,[],[f22148,f22187,f22168])).

fof(f22168,plain,
    ( spl33_267
  <=> k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_267])])).

fof(f22187,plain,
    ( spl33_271
  <=> ! [X104,X103] :
        ( r1_tarski(sK14(X103,k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X104))
        | ~ m1_subset_1(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X103)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_271])])).

fof(f22148,plain,(
    ! [X103,X104] :
      ( r1_tarski(sK14(X103,k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X104))
      | ~ m1_subset_1(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X103))
      | k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f2911,f3781])).

fof(f3781,plain,(
    ! [X19,X18] :
      ( r1_tarski(sK14(X19,k1_zfmisc_1(X18)),X18)
      | ~ m1_subset_1(k1_zfmisc_1(X18),k1_zfmisc_1(X19))
      | k1_xboole_0 = k1_zfmisc_1(X18) ) ),
    inference(resolution,[],[f2061,f2227])).

fof(f2061,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(X0,X1),X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1950])).

fof(f1950,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(sK14(X0,X1),X1)
        & m1_subset_1(sK14(X0,X1),X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f1808,f1949])).

fof(f1949,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
     => ( r2_hidden(sK14(X0,X1),X1)
        & m1_subset_1(sK14(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1808,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f1807])).

fof(f1807,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r2_hidden(X2,X1)
          & m1_subset_1(X2,X0) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f497])).

fof(f497,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ~ ( ! [X2] :
              ( m1_subset_1(X2,X0)
             => ~ r2_hidden(X2,X1) )
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_subset_1)).

fof(f22182,plain,
    ( spl33_267
    | spl33_270 ),
    inference(avatar_split_clause,[],[f22112,f22180,f22168])).

fof(f22180,plain,
    ( spl33_270
  <=> ! [X55] : r1_tarski(sK15(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X55)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_270])])).

fof(f22112,plain,(
    ! [X55] :
      ( r1_tarski(sK15(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X55))
      | k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f2911,f2598])).

fof(f2598,plain,(
    ! [X6] :
      ( r1_tarski(sK15(k1_zfmisc_1(X6)),X6)
      | k1_xboole_0 = k1_zfmisc_1(X6) ) ),
    inference(resolution,[],[f2227,f2066])).

fof(f2066,plain,(
    ! [X0] :
      ( r2_hidden(sK15(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1952])).

fof(f1952,plain,(
    ! [X0] :
      ( r2_hidden(sK15(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f1812,f1951])).

fof(f1951,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK15(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f1812,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f22178,plain,
    ( spl33_267
    | spl33_269 ),
    inference(avatar_split_clause,[],[f22109,f22176,f22168])).

fof(f22176,plain,
    ( spl33_269
  <=> ! [X51,X50] :
        ( r1_tarski(sK13(k1_zfmisc_1(k1_tarski(k1_xboole_0)),X50),k1_zfmisc_1(X51))
        | k1_zfmisc_1(k1_tarski(k1_xboole_0)) = k1_tarski(X50) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_269])])).

fof(f22109,plain,(
    ! [X50,X51] :
      ( r1_tarski(sK13(k1_zfmisc_1(k1_tarski(k1_xboole_0)),X50),k1_zfmisc_1(X51))
      | k1_zfmisc_1(k1_tarski(k1_xboole_0)) = k1_tarski(X50)
      | k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f2911,f3682])).

fof(f3682,plain,(
    ! [X19,X18] :
      ( r1_tarski(sK13(k1_zfmisc_1(X18),X19),X18)
      | k1_zfmisc_1(X18) = k1_tarski(X19)
      | k1_xboole_0 = k1_zfmisc_1(X18) ) ),
    inference(resolution,[],[f2046,f2227])).

fof(f2046,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f1942])).

fof(f1942,plain,(
    ! [X0,X1] :
      ( ( sK13(X0,X1) != X1
        & r2_hidden(sK13(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f1803,f1941])).

fof(f1941,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK13(X0,X1) != X1
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1803,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f314])).

fof(f314,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f22174,plain,
    ( spl33_267
    | spl33_268 ),
    inference(avatar_split_clause,[],[f22108,f22172,f22168])).

fof(f22172,plain,
    ( spl33_268
  <=> ! [X49,X48] :
        ( r1_tarski(sK12(k1_zfmisc_1(k1_tarski(k1_xboole_0)),X48),k1_zfmisc_1(X49))
        | k1_zfmisc_1(k1_tarski(k1_xboole_0)) = k1_tarski(X48) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_268])])).

fof(f22108,plain,(
    ! [X48,X49] :
      ( r1_tarski(sK12(k1_zfmisc_1(k1_tarski(k1_xboole_0)),X48),k1_zfmisc_1(X49))
      | k1_zfmisc_1(k1_tarski(k1_xboole_0)) = k1_tarski(X48)
      | k1_xboole_0 = k1_zfmisc_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f2911,f3653])).

fof(f3653,plain,(
    ! [X19,X18] :
      ( r1_tarski(sK12(k1_zfmisc_1(X18),X19),X18)
      | k1_zfmisc_1(X18) = k1_tarski(X19)
      | k1_xboole_0 = k1_zfmisc_1(X18) ) ),
    inference(resolution,[],[f2044,f2227])).

fof(f2044,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),X0)
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f1940])).

fof(f1940,plain,(
    ! [X0,X1] :
      ( ( sK12(X0,X1) != X1
        & r2_hidden(sK12(X0,X1),X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f1802,f1939])).

fof(f1939,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
     => ( sK12(X0,X1) != X1
        & r2_hidden(sK12(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f1802,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f399])).

fof(f399,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f22166,plain,
    ( spl33_265
    | spl33_266 ),
    inference(avatar_split_clause,[],[f22104,f22164,f22161])).

fof(f22161,plain,
    ( spl33_265
  <=> ! [X41] : ~ r2_hidden(X41,k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_265])])).

fof(f22164,plain,
    ( spl33_266
  <=> ! [X40] : r1_tarski(sK3(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X40)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_266])])).

fof(f22104,plain,(
    ! [X41,X40] :
      ( r1_tarski(sK3(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_zfmisc_1(X40))
      | ~ r2_hidden(X41,k1_zfmisc_1(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f2911,f2597])).

fof(f2597,plain,(
    ! [X4,X5] :
      ( r1_tarski(sK3(k1_zfmisc_1(X4)),X4)
      | ~ r2_hidden(X5,k1_zfmisc_1(X4)) ) ),
    inference(resolution,[],[f2227,f2008])).

fof(f2008,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1913])).

fof(f1913,plain,(
    ! [X0,X1] :
      ( ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1778,f1912])).

fof(f1912,plain,(
    ! [X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
     => ( ! [X3] :
            ( ~ r2_hidden(X3,sK3(X1))
            | ~ r2_hidden(X3,X1) )
        & r2_hidden(sK3(X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f1778,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f433])).

fof(f433,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

fof(f19611,plain,
    ( spl33_264
    | ~ spl33_4
    | spl33_47
    | ~ spl33_60
    | ~ spl33_64 ),
    inference(avatar_split_clause,[],[f19610,f5858,f5757,f3401,f2259,f19584])).

fof(f19584,plain,
    ( spl33_264
  <=> k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_264])])).

fof(f5757,plain,
    ( spl33_60
  <=> r1_tarski(sK15(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_60])])).

fof(f5858,plain,
    ( spl33_64
  <=> k1_xboole_0 = sK15(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_64])])).

fof(f19610,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | spl33_47
    | ~ spl33_60
    | ~ spl33_64 ),
    inference(forward_demodulation,[],[f19609,f5860])).

fof(f5860,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ spl33_64 ),
    inference(avatar_component_clause,[],[f5858])).

fof(f19609,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | spl33_47
    | ~ spl33_60
    | ~ spl33_64 ),
    inference(subsumption_resolution,[],[f19608,f3402])).

fof(f19608,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_60
    | ~ spl33_64 ),
    inference(forward_demodulation,[],[f19561,f5860])).

fof(f19561,plain,
    ( k1_tarski(k1_xboole_0) = sK15(k1_tarski(k1_xboole_0))
    | k1_xboole_0 = sK4(k1_xboole_0,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_60 ),
    inference(resolution,[],[f4140,f5867])).

fof(f5867,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_60 ),
    inference(subsumption_resolution,[],[f5849,f2355])).

fof(f5849,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK15(k1_tarski(k1_xboole_0)))
        | r2_hidden(X1,k1_xboole_0) )
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2015])).

fof(f5759,plain,
    ( r1_tarski(sK15(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_60 ),
    inference(avatar_component_clause,[],[f5757])).

fof(f4140,plain,
    ( ! [X19] :
        ( r2_hidden(sK4(k1_xboole_0,X19),X19)
        | k1_tarski(k1_xboole_0) = X19
        | k1_xboole_0 = sK4(k1_xboole_0,X19) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f4134,f2261])).

fof(f4134,plain,(
    ! [X19] :
      ( k1_zfmisc_1(k1_xboole_0) = X19
      | r2_hidden(sK4(k1_xboole_0,X19),X19)
      | k1_xboole_0 = sK4(k1_xboole_0,X19) ) ),
    inference(resolution,[],[f2013,f2075])).

fof(f2013,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK4(X0,X1),X0)
      | k1_zfmisc_1(X0) = X1
      | r2_hidden(sK4(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f1917])).

fof(f19602,plain,
    ( spl33_264
    | ~ spl33_4
    | spl33_47
    | ~ spl33_59
    | ~ spl33_61 ),
    inference(avatar_split_clause,[],[f19601,f5808,f5752,f3401,f2259,f19584])).

fof(f5752,plain,
    ( spl33_59
  <=> r1_tarski(sK3(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_59])])).

fof(f5808,plain,
    ( spl33_61
  <=> k1_xboole_0 = sK3(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_61])])).

fof(f19601,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | spl33_47
    | ~ spl33_59
    | ~ spl33_61 ),
    inference(forward_demodulation,[],[f19600,f5810])).

fof(f5810,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ spl33_61 ),
    inference(avatar_component_clause,[],[f5808])).

fof(f19600,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | spl33_47
    | ~ spl33_59
    | ~ spl33_61 ),
    inference(subsumption_resolution,[],[f19599,f3402])).

fof(f19599,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_59
    | ~ spl33_61 ),
    inference(forward_demodulation,[],[f19555,f5810])).

fof(f19555,plain,
    ( k1_tarski(k1_xboole_0) = sK3(k1_tarski(k1_xboole_0))
    | k1_xboole_0 = sK4(k1_xboole_0,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_59 ),
    inference(resolution,[],[f4140,f5817])).

fof(f5817,plain,
    ( ! [X1] : ~ r2_hidden(X1,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_59 ),
    inference(subsumption_resolution,[],[f5799,f2355])).

fof(f5799,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,sK3(k1_tarski(k1_xboole_0)))
        | r2_hidden(X1,k1_xboole_0) )
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2015])).

fof(f5754,plain,
    ( r1_tarski(sK3(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_59 ),
    inference(avatar_component_clause,[],[f5752])).

fof(f19596,plain,
    ( spl33_264
    | ~ spl33_4
    | spl33_47
    | ~ spl33_121 ),
    inference(avatar_split_clause,[],[f19595,f10100,f3401,f2259,f19584])).

fof(f10100,plain,
    ( spl33_121
  <=> k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_121])])).

fof(f19595,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | spl33_47
    | ~ spl33_121 ),
    inference(forward_demodulation,[],[f19594,f10102])).

fof(f10102,plain,
    ( k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0))
    | ~ spl33_121 ),
    inference(avatar_component_clause,[],[f10100])).

fof(f19594,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | spl33_47
    | ~ spl33_121 ),
    inference(subsumption_resolution,[],[f19593,f3402])).

fof(f19593,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_121 ),
    inference(forward_demodulation,[],[f19540,f10102])).

fof(f19540,plain,
    ( k1_tarski(k1_xboole_0) = k3_tarski(k1_tarski(k1_xboole_0))
    | k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(resolution,[],[f4140,f10046])).

fof(f10046,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f10041,f2010])).

fof(f10041,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_tarski(k1_xboole_0)),X0) ),
    inference(subsumption_resolution,[],[f10020,f2077])).

fof(f10020,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k1_tarski(k1_xboole_0)),X0)
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f9665,f2222])).

fof(f9665,plain,(
    ! [X8] : r1_tarski(k5_setfam_1(X8,k1_tarski(k1_xboole_0)),X8) ),
    inference(resolution,[],[f3560,f2077])).

fof(f19592,plain,
    ( spl33_264
    | ~ spl33_4
    | spl33_47
    | ~ spl33_112 ),
    inference(avatar_split_clause,[],[f19591,f9811,f3401,f2259,f19584])).

fof(f19591,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | spl33_47
    | ~ spl33_112 ),
    inference(forward_demodulation,[],[f19590,f9813])).

fof(f19590,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_xboole_0))
    | ~ spl33_4
    | spl33_47
    | ~ spl33_112 ),
    inference(subsumption_resolution,[],[f19589,f3402])).

fof(f19589,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_112 ),
    inference(forward_demodulation,[],[f19539,f9813])).

fof(f19539,plain,
    ( k1_tarski(k1_xboole_0) = k3_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,k3_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(resolution,[],[f4140,f9751])).

fof(f9751,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f9746,f2010])).

fof(f9746,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f9725,f2078])).

fof(f9725,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k1_xboole_0),X0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f9664,f2222])).

fof(f19587,plain,
    ( spl33_264
    | ~ spl33_4
    | spl33_47 ),
    inference(avatar_split_clause,[],[f19582,f3401,f2259,f19584])).

fof(f19582,plain,
    ( k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4
    | spl33_47 ),
    inference(subsumption_resolution,[],[f19519,f3402])).

fof(f19519,plain,
    ( k1_xboole_0 = k1_tarski(k1_xboole_0)
    | k1_xboole_0 = sK4(k1_xboole_0,k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f4140,f2355])).

fof(f18188,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18187])).

fof(f18187,plain,
    ( $false
    | ~ spl33_262 ),
    inference(subsumption_resolution,[],[f18058,f18019])).

fof(f18019,plain,
    ( ! [X15,X18] : ~ r1_tarski(X18,X15)
    | ~ spl33_262 ),
    inference(avatar_component_clause,[],[f18018])).

fof(f18018,plain,
    ( spl33_262
  <=> ! [X18,X15] : ~ r1_tarski(X18,X15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_262])])).

fof(f18058,plain,
    ( ! [X8,X7] : r1_tarski(k1_zfmisc_1(X7),X8)
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2624])).

fof(f2624,plain,(
    ! [X10,X9] :
      ( r1_tarski(sK5(k1_zfmisc_1(X9),X10),X9)
      | r1_tarski(k1_zfmisc_1(X9),X10) ) ),
    inference(resolution,[],[f2016,f2227])).

fof(f2016,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1921])).

fof(f18186,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18029])).

fof(f18029,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2234])).

fof(f18185,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18030])).

fof(f18030,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2079])).

fof(f18184,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18031])).

fof(f18031,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9746])).

fof(f18183,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18032])).

fof(f18032,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10041])).

fof(f18182,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18033])).

fof(f18033,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10265])).

fof(f10265,plain,(
    ! [X0] : r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0) ),
    inference(subsumption_resolution,[],[f10255,f2550])).

fof(f10255,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(k1_zfmisc_1(X0)),X0)
      | ~ m1_subset_1(k1_zfmisc_1(X0),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f9662,f2222])).

fof(f9662,plain,(
    ! [X4] : r1_tarski(k5_setfam_1(X4,k1_zfmisc_1(X4)),X4) ),
    inference(resolution,[],[f3560,f2550])).

fof(f18181,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18034])).

fof(f18034,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10337])).

fof(f10337,plain,(
    ! [X31] : r1_tarski(k3_tarski(k1_zfmisc_1(sK26(X31))),X31) ),
    inference(resolution,[],[f10265,f2900])).

fof(f2900,plain,(
    ! [X12,X11] :
      ( ~ r1_tarski(X11,sK26(X12))
      | r1_tarski(X11,X12) ) ),
    inference(resolution,[],[f2113,f2467])).

fof(f2467,plain,(
    ! [X7] : r1_tarski(sK26(X7),X7) ),
    inference(resolution,[],[f2106,f2143])).

fof(f18180,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18035])).

fof(f18035,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f11889])).

fof(f11889,plain,(
    ! [X0] : r1_tarski(k3_tarski(sK26(k1_zfmisc_1(X0))),X0) ),
    inference(subsumption_resolution,[],[f11863,f2143])).

fof(f11863,plain,(
    ! [X0] :
      ( r1_tarski(k3_tarski(sK26(k1_zfmisc_1(X0))),X0)
      | ~ m1_subset_1(sK26(k1_zfmisc_1(X0)),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f9687,f2222])).

fof(f9687,plain,(
    ! [X48] : r1_tarski(k5_setfam_1(X48,sK26(k1_zfmisc_1(X48))),X48) ),
    inference(resolution,[],[f3560,f2143])).

fof(f18179,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18036])).

fof(f18036,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f11927])).

fof(f11927,plain,(
    ! [X34] : r1_tarski(k3_tarski(sK26(k1_zfmisc_1(sK26(X34)))),X34) ),
    inference(resolution,[],[f11889,f2900])).

fof(f18178,plain,
    ( ~ spl33_4
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18037])).

fof(f18037,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f11951])).

fof(f11951,plain,
    ( ! [X15] : r1_tarski(k3_tarski(sK26(k1_tarski(k1_xboole_0))),X15)
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11915,f2261])).

fof(f11915,plain,(
    ! [X15] : r1_tarski(k3_tarski(sK26(k1_zfmisc_1(k1_xboole_0))),X15) ),
    inference(resolution,[],[f11889,f2896])).

fof(f2896,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f2113,f2079])).

fof(f18177,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18038])).

fof(f18038,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f12147])).

fof(f12147,plain,(
    ! [X4] : r1_tarski(k3_tarski(sK28(k1_zfmisc_1(X4))),X4) ),
    inference(resolution,[],[f9867,f2106])).

fof(f18176,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18039])).

fof(f18039,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f12216])).

fof(f12216,plain,(
    ! [X34] : r1_tarski(k3_tarski(sK28(k1_zfmisc_1(sK26(X34)))),X34) ),
    inference(resolution,[],[f12147,f2900])).

fof(f18175,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18042])).

fof(f18042,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9664])).

fof(f18174,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18043])).

fof(f18043,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9713])).

fof(f9713,plain,(
    ! [X15] : r1_tarski(k5_setfam_1(k1_xboole_0,k1_xboole_0),X15) ),
    inference(resolution,[],[f9664,f2896])).

fof(f18173,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18044])).

fof(f18044,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9723])).

fof(f9723,plain,(
    ! [X31] : r1_tarski(k5_setfam_1(sK26(X31),k1_xboole_0),X31) ),
    inference(resolution,[],[f9664,f2900])).

fof(f18172,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18045])).

fof(f18045,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10519])).

fof(f10519,plain,(
    ! [X33] : r1_tarski(k5_setfam_1(sK26(sK26(X33)),k1_xboole_0),X33) ),
    inference(resolution,[],[f9723,f2900])).

fof(f18171,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18046])).

fof(f18046,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9665])).

fof(f18170,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18047])).

fof(f18047,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10008])).

fof(f10008,plain,(
    ! [X15] : r1_tarski(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0)),X15) ),
    inference(resolution,[],[f9665,f2896])).

fof(f18169,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18048])).

fof(f18048,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f10018])).

fof(f10018,plain,(
    ! [X31] : r1_tarski(k5_setfam_1(sK26(X31),k1_tarski(k1_xboole_0)),X31) ),
    inference(resolution,[],[f9665,f2900])).

fof(f18168,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18049])).

fof(f18049,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9662])).

fof(f18167,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18050])).

fof(f18050,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9687])).

fof(f18166,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18051])).

fof(f18051,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9698])).

fof(f9698,plain,(
    ! [X51] : r1_tarski(k5_setfam_1(X51,sK28(k1_zfmisc_1(X51))),X51) ),
    inference(subsumption_resolution,[],[f9690,f2160])).

fof(f9690,plain,(
    ! [X51] :
      ( r1_tarski(k5_setfam_1(X51,sK28(k1_zfmisc_1(X51))),X51)
      | v1_xboole_0(k1_zfmisc_1(X51)) ) ),
    inference(resolution,[],[f3560,f2156])).

fof(f18165,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18052])).

fof(f18052,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2203])).

fof(f2203,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f796])).

fof(f796,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f18164,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18053])).

fof(f18053,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3854])).

fof(f3854,plain,(
    ! [X2,X3] : r1_tarski(k1_relat_1(k2_zfmisc_1(sK26(X2),X3)),X2) ),
    inference(resolution,[],[f2900,f2203])).

fof(f18163,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18054])).

fof(f18054,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2412])).

fof(f2412,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[],[f2203,f2228])).

fof(f18162,plain,
    ( ~ spl33_59
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18055])).

fof(f18055,plain,
    ( $false
    | ~ spl33_59
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f5796])).

fof(f5796,plain,
    ( ! [X0] : r1_tarski(sK3(k1_tarski(k1_xboole_0)),X0)
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2896])).

fof(f18161,plain,
    ( ~ spl33_60
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18060])).

fof(f18060,plain,
    ( $false
    | ~ spl33_60
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f5846])).

fof(f5846,plain,
    ( ! [X0] : r1_tarski(sK15(k1_tarski(k1_xboole_0)),X0)
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2896])).

fof(f18160,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18062])).

fof(f18062,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2466])).

fof(f2466,plain,(
    ! [X6] : r1_tarski(sK22(k1_zfmisc_1(X6)),X6) ),
    inference(resolution,[],[f2106,f2108])).

fof(f18159,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18063])).

fof(f18063,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3856])).

fof(f3856,plain,(
    ! [X5] : r1_tarski(sK22(k1_zfmisc_1(sK26(X5))),X5) ),
    inference(resolution,[],[f2900,f2466])).

fof(f18158,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18064])).

fof(f18064,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3923])).

fof(f3923,plain,(
    ! [X12] : r1_tarski(sK22(k1_zfmisc_1(sK26(sK26(X12)))),X12) ),
    inference(resolution,[],[f3856,f2900])).

fof(f18157,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18065])).

fof(f18065,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8330])).

fof(f8330,plain,(
    ! [X4] : r1_tarski(sK22(sK28(k1_zfmisc_1(X4))),X4) ),
    inference(subsumption_resolution,[],[f8307,f2160])).

fof(f8307,plain,(
    ! [X4] :
      ( v1_xboole_0(k1_zfmisc_1(X4))
      | r1_tarski(sK22(sK28(k1_zfmisc_1(X4))),X4) ) ),
    inference(resolution,[],[f8303,f2106])).

fof(f18156,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18066])).

fof(f18066,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8469])).

fof(f8469,plain,(
    ! [X22] : r1_tarski(sK22(sK28(k1_zfmisc_1(sK26(X22)))),X22) ),
    inference(resolution,[],[f8330,f2900])).

fof(f18155,plain,
    ( ~ spl33_4
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18067])).

fof(f18067,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8475])).

fof(f8475,plain,
    ( ! [X15] : r1_tarski(sK22(sK28(k1_tarski(k1_xboole_0))),X15)
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f8463,f2261])).

fof(f8463,plain,(
    ! [X15] : r1_tarski(sK22(sK28(k1_zfmisc_1(k1_xboole_0))),X15) ),
    inference(resolution,[],[f8330,f2896])).

fof(f18154,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18068])).

fof(f18068,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2467])).

fof(f18153,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18069])).

fof(f18069,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3857])).

fof(f3857,plain,(
    ! [X6] : r1_tarski(sK26(sK26(X6)),X6) ),
    inference(resolution,[],[f2900,f2467])).

fof(f18152,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18070])).

fof(f18070,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3877])).

fof(f3877,plain,(
    ! [X12] : r1_tarski(sK26(sK26(sK26(X12))),X12) ),
    inference(resolution,[],[f3857,f2900])).

fof(f18151,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18071])).

fof(f18071,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3983])).

fof(f3983,plain,(
    ! [X12] : r1_tarski(sK26(sK26(sK26(sK26(X12)))),X12) ),
    inference(resolution,[],[f3877,f2900])).

fof(f18150,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18072])).

fof(f18072,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f7782])).

fof(f7782,plain,(
    ! [X26,X27] : r1_tarski(sK26(k1_relat_1(k2_zfmisc_1(X26,X27))),X26) ),
    inference(resolution,[],[f2897,f2467])).

fof(f2897,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X4,k1_relat_1(k2_zfmisc_1(X5,X6)))
      | r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f2113,f2203])).

fof(f18149,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18074])).

fof(f18074,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2470])).

fof(f2470,plain,(
    ! [X8] : r1_tarski(sK27(k1_zfmisc_1(X8)),X8) ),
    inference(subsumption_resolution,[],[f2468,f2160])).

fof(f2468,plain,(
    ! [X8] :
      ( r1_tarski(sK27(k1_zfmisc_1(X8)),X8)
      | v1_xboole_0(k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f2106,f2407])).

fof(f2407,plain,(
    ! [X1] :
      ( m1_subset_1(sK27(X1),X1)
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f2146,f2034])).

fof(f18148,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18075])).

fof(f18075,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3858])).

fof(f3858,plain,(
    ! [X7] : r1_tarski(sK27(k1_zfmisc_1(sK26(X7))),X7) ),
    inference(resolution,[],[f2900,f2470])).

fof(f18147,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18076])).

fof(f18076,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f3947])).

fof(f3947,plain,(
    ! [X12] : r1_tarski(sK27(k1_zfmisc_1(sK26(sK26(X12)))),X12) ),
    inference(resolution,[],[f3858,f2900])).

fof(f18146,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18077])).

fof(f18077,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8542])).

fof(f8542,plain,(
    ! [X4] : r1_tarski(sK27(sK28(k1_zfmisc_1(X4))),X4) ),
    inference(subsumption_resolution,[],[f8518,f2160])).

fof(f8518,plain,(
    ! [X4] :
      ( v1_xboole_0(k1_zfmisc_1(X4))
      | r1_tarski(sK27(sK28(k1_zfmisc_1(X4))),X4) ) ),
    inference(resolution,[],[f8304,f2106])).

fof(f18145,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18078])).

fof(f18078,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8652])).

fof(f8652,plain,(
    ! [X24] : r1_tarski(sK27(sK28(k1_zfmisc_1(sK26(X24)))),X24) ),
    inference(resolution,[],[f8542,f2900])).

fof(f18144,plain,
    ( ~ spl33_4
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18079])).

fof(f18079,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8658])).

fof(f8658,plain,
    ( ! [X15] : r1_tarski(sK27(sK28(k1_tarski(k1_xboole_0))),X15)
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f8645,f2261])).

fof(f8645,plain,(
    ! [X15] : r1_tarski(sK27(sK28(k1_zfmisc_1(k1_xboole_0))),X15) ),
    inference(resolution,[],[f8542,f2896])).

fof(f18143,plain,
    ( ~ spl33_59
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18100])).

fof(f18100,plain,
    ( $false
    | ~ spl33_59
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f5754])).

fof(f18142,plain,
    ( ~ spl33_60
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18101])).

fof(f18101,plain,
    ( $false
    | ~ spl33_60
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f5759])).

fof(f18141,plain,
    ( ~ spl33_27
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18102])).

fof(f18102,plain,
    ( $false
    | ~ spl33_27
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2495])).

fof(f2495,plain,
    ( r1_tarski(sK22(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_27 ),
    inference(avatar_component_clause,[],[f2493])).

fof(f2493,plain,
    ( spl33_27
  <=> r1_tarski(sK22(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_27])])).

fof(f18140,plain,
    ( ~ spl33_89
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18103])).

fof(f18103,plain,
    ( $false
    | ~ spl33_89
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8359])).

fof(f8359,plain,
    ( r1_tarski(sK22(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_89 ),
    inference(avatar_component_clause,[],[f8357])).

fof(f8357,plain,
    ( spl33_89
  <=> r1_tarski(sK22(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_89])])).

fof(f18139,plain,
    ( ~ spl33_29
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18104])).

fof(f18104,plain,
    ( $false
    | ~ spl33_29
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2509])).

fof(f2509,plain,
    ( r1_tarski(sK27(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_29 ),
    inference(avatar_component_clause,[],[f2507])).

fof(f2507,plain,
    ( spl33_29
  <=> r1_tarski(sK27(k1_tarski(k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_29])])).

fof(f18138,plain,
    ( ~ spl33_95
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18105])).

fof(f18105,plain,
    ( $false
    | ~ spl33_95
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f8577])).

fof(f8577,plain,
    ( r1_tarski(sK27(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_95 ),
    inference(avatar_component_clause,[],[f8575])).

fof(f8575,plain,
    ( spl33_95
  <=> r1_tarski(sK27(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_95])])).

fof(f18137,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18106])).

fof(f18106,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2231])).

fof(f2231,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f2052])).

fof(f2052,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f1946])).

fof(f1946,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f1945])).

fof(f1945,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f313])).

fof(f313,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f18136,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18107])).

fof(f18107,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2230])).

fof(f2230,plain,(
    ! [X1] : r1_tarski(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f2053])).

fof(f2053,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f1946])).

fof(f18135,plain,
    ( ~ spl33_72
    | ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18108])).

fof(f18108,plain,
    ( $false
    | ~ spl33_72
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6655])).

fof(f6655,plain,
    ( r1_tarski(sK28(k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | ~ spl33_72 ),
    inference(avatar_component_clause,[],[f6653])).

fof(f6653,plain,
    ( spl33_72
  <=> r1_tarski(sK28(k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_72])])).

fof(f18134,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18110])).

fof(f18110,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2200])).

fof(f18133,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18111])).

fof(f18111,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f2465])).

fof(f18132,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18114])).

fof(f18114,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f9716])).

fof(f9716,plain,(
    ! [X18] : r1_tarski(k5_setfam_1(k1_tarski(X18),k1_xboole_0),k1_zfmisc_1(X18)) ),
    inference(resolution,[],[f9664,f2910])).

fof(f2910,plain,(
    ! [X33,X32] :
      ( ~ r1_tarski(X32,k1_tarski(X33))
      | r1_tarski(X32,k1_zfmisc_1(X33)) ) ),
    inference(resolution,[],[f2113,f2200])).

fof(f18131,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18116])).

fof(f18116,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6602])).

fof(f6602,plain,(
    ! [X13] : r1_tarski(sK22(k1_zfmisc_1(k1_tarski(X13))),k1_zfmisc_1(X13)) ),
    inference(resolution,[],[f2910,f2466])).

fof(f18130,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18117])).

fof(f18117,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6605])).

fof(f6605,plain,(
    ! [X16] : r1_tarski(sK26(k1_tarski(X16)),k1_zfmisc_1(X16)) ),
    inference(resolution,[],[f2910,f2467])).

fof(f18129,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18118])).

fof(f18118,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6606])).

fof(f6606,plain,(
    ! [X17] : r1_tarski(sK26(sK26(k1_tarski(X17))),k1_zfmisc_1(X17)) ),
    inference(resolution,[],[f2910,f3857])).

fof(f18128,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18119])).

fof(f18119,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6609])).

fof(f6609,plain,(
    ! [X20] : r1_tarski(sK27(k1_zfmisc_1(k1_tarski(X20))),k1_zfmisc_1(X20)) ),
    inference(resolution,[],[f2910,f2470])).

fof(f18127,plain,(
    ~ spl33_262 ),
    inference(avatar_contradiction_clause,[],[f18120])).

fof(f18120,plain,
    ( $false
    | ~ spl33_262 ),
    inference(resolution,[],[f18019,f6621])).

fof(f6621,plain,(
    ! [X23] : r1_tarski(sK28(k1_tarski(X23)),k1_zfmisc_1(X23)) ),
    inference(subsumption_resolution,[],[f6612,f2161])).

fof(f6612,plain,(
    ! [X23] :
      ( r1_tarski(sK28(k1_tarski(X23)),k1_zfmisc_1(X23))
      | v1_xboole_0(k1_tarski(X23)) ) ),
    inference(resolution,[],[f2910,f2539])).

fof(f2539,plain,(
    ! [X0] :
      ( r1_tarski(sK28(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2156,f2106])).

fof(f18023,plain,
    ( spl33_262
    | spl33_263
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f17992,f2259,f18021,f18018])).

fof(f18021,plain,
    ( spl33_263
  <=> ! [X16,X17] :
        ( m1_subset_1(X17,k1_zfmisc_1(X16))
        | ~ v1_xboole_0(X16)
        | ~ m1_subset_1(X17,k1_tarski(k1_xboole_0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_263])])).

fof(f17992,plain,
    ( ! [X17,X15,X18,X16] :
        ( m1_subset_1(X17,k1_zfmisc_1(X16))
        | ~ r1_tarski(X18,X15)
        | ~ m1_subset_1(X17,k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X16) )
    | ~ spl33_4 ),
    inference(superposition,[],[f5323,f2354])).

fof(f5323,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
        | ~ r1_tarski(X0,X3)
        | ~ m1_subset_1(X1,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f5322,f2261])).

fof(f5322,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(subsumption_resolution,[],[f5315,f2079])).

fof(f5315,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_xboole_0,X2)
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) ) ),
    inference(superposition,[],[f2103,f2228])).

fof(f2103,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(cnf_transformation,[],[f1822])).

fof(f1822,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1821])).

fof(f1821,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1243])).

fof(f1243,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f18012,plain,
    ( spl33_260
    | spl33_261
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f17984,f2259,f18010,f18007])).

fof(f18007,plain,
    ( spl33_260
  <=> ! [X79] :
        ( ~ m1_subset_1(X79,k1_tarski(k1_xboole_0))
        | v1_relat_1(k1_tarski(X79)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_260])])).

fof(f18010,plain,
    ( spl33_261
  <=> ! [X77,X78,X80] :
        ( ~ r1_tarski(X77,X78)
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X78,X80)))
        | k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X78,X80)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_261])])).

fof(f17984,plain,
    ( ! [X80,X78,X79,X77] :
        ( ~ r1_tarski(X77,X78)
        | ~ m1_subset_1(X79,k1_tarski(k1_xboole_0))
        | k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X78,X80))
        | v1_relat_1(k1_tarski(X79))
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X78,X80))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f5323,f3432])).

fof(f3432,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X11,X10)
      | k1_xboole_0 = X10
      | v1_relat_1(k1_tarski(X11))
      | ~ v1_relat_1(X10) ) ),
    inference(resolution,[],[f2062,f2110])).

fof(f18005,plain,
    ( spl33_258
    | spl33_259
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f17983,f2259,f18003,f18000])).

fof(f18000,plain,
    ( spl33_258
  <=> ! [X75] :
        ( ~ m1_subset_1(X75,k1_tarski(k1_xboole_0))
        | v1_funct_1(k1_tarski(X75)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_258])])).

fof(f18003,plain,
    ( spl33_259
  <=> ! [X73,X74,X76] :
        ( ~ r1_tarski(X73,X74)
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X74,X76)))
        | ~ v1_funct_1(k1_zfmisc_1(k2_zfmisc_1(X74,X76)))
        | k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X74,X76)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_259])])).

fof(f17983,plain,
    ( ! [X76,X74,X75,X73] :
        ( ~ r1_tarski(X73,X74)
        | ~ m1_subset_1(X75,k1_tarski(k1_xboole_0))
        | k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X74,X76))
        | v1_funct_1(k1_tarski(X75))
        | ~ v1_funct_1(k1_zfmisc_1(k2_zfmisc_1(X74,X76)))
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X74,X76))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f5323,f3431])).

fof(f16219,plain,
    ( spl33_56
    | spl33_255 ),
    inference(avatar_split_clause,[],[f16171,f16208,f4925])).

fof(f4925,plain,
    ( spl33_56
  <=> ! [X7] : ~ v1_xboole_0(X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_56])])).

fof(f16208,plain,
    ( spl33_255
  <=> ! [X12] :
        ( ~ v1_xboole_0(X12)
        | v1_relat_1(k5_setfam_1(X12,X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_255])])).

fof(f16171,plain,(
    ! [X24,X25] :
      ( ~ v1_xboole_0(X24)
      | v1_relat_1(k5_setfam_1(X24,X24))
      | ~ v1_xboole_0(X25) ) ),
    inference(resolution,[],[f9942,f3352])).

fof(f9942,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_setfam_1(X0,X0),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f9713,f2152])).

fof(f16218,plain,
    ( spl33_110
    | spl33_257 ),
    inference(avatar_split_clause,[],[f16170,f16216,f9799])).

fof(f9799,plain,
    ( spl33_110
  <=> ! [X13] :
        ( ~ v1_funct_1(X13)
        | ~ v1_relat_1(X13) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_110])])).

fof(f16216,plain,
    ( spl33_257
  <=> ! [X22] :
        ( ~ v1_xboole_0(X22)
        | v1_funct_1(k5_setfam_1(X22,X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_257])])).

fof(f16170,plain,(
    ! [X23,X22] :
      ( ~ v1_xboole_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X23)
      | v1_funct_1(k5_setfam_1(X22,X22)) ) ),
    inference(resolution,[],[f9942,f3134])).

fof(f16214,plain,
    ( spl33_56
    | spl33_256 ),
    inference(avatar_split_clause,[],[f16167,f16212,f4925])).

fof(f16212,plain,
    ( spl33_256
  <=> ! [X14] :
        ( ~ v1_xboole_0(X14)
        | v1_xboole_0(k5_setfam_1(X14,X14)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_256])])).

fof(f16167,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ v1_xboole_0(X15)
      | v1_xboole_0(k5_setfam_1(X14,X14)) ) ),
    inference(resolution,[],[f9942,f2782])).

fof(f16210,plain,
    ( spl33_107
    | spl33_255 ),
    inference(avatar_split_clause,[],[f16166,f16208,f9786])).

fof(f9786,plain,
    ( spl33_107
  <=> ! [X7] : ~ v1_relat_1(X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_107])])).

fof(f16166,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | ~ v1_relat_1(X13)
      | v1_relat_1(k5_setfam_1(X12,X12)) ) ),
    inference(resolution,[],[f9942,f2716])).

fof(f14660,plain,
    ( ~ spl33_10
    | ~ spl33_101 ),
    inference(avatar_contradiction_clause,[],[f14659])).

fof(f14659,plain,
    ( $false
    | ~ spl33_10
    | ~ spl33_101 ),
    inference(subsumption_resolution,[],[f14658,f2161])).

fof(f14658,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl33_10
    | ~ spl33_101 ),
    inference(subsumption_resolution,[],[f14559,f2291])).

fof(f14559,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl33_101 ),
    inference(superposition,[],[f2157,f9476])).

fof(f9476,plain,
    ( k1_xboole_0 = sK28(k1_tarski(k1_xboole_0))
    | ~ spl33_101 ),
    inference(avatar_component_clause,[],[f9474])).

fof(f14657,plain,
    ( spl33_249
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14557,f9474,f14625])).

fof(f14625,plain,
    ( spl33_249
  <=> k1_xboole_0 = sK27(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_249])])).

fof(f14557,plain,
    ( k1_xboole_0 = sK27(k1_xboole_0)
    | ~ spl33_101 ),
    inference(superposition,[],[f9081,f9476])).

fof(f9081,plain,(
    ! [X22] : sK27(sK28(k1_tarski(X22))) = X22 ),
    inference(subsumption_resolution,[],[f9051,f2161])).

fof(f9051,plain,(
    ! [X22] :
      ( v1_xboole_0(k1_tarski(X22))
      | sK27(sK28(k1_tarski(X22))) = X22 ) ),
    inference(resolution,[],[f8539,f2238])).

fof(f2238,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f2177])).

fof(f2177,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1991])).

fof(f14656,plain,
    ( ~ spl33_254
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14556,f9474,f14653])).

fof(f14653,plain,
    ( spl33_254
  <=> r2_hidden(k1_xboole_0,sK27(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_254])])).

fof(f14556,plain,
    ( ~ r2_hidden(k1_xboole_0,sK27(k1_xboole_0))
    | ~ spl33_101 ),
    inference(superposition,[],[f9080,f9476])).

fof(f9080,plain,(
    ! [X21] : ~ r2_hidden(X21,sK27(sK28(k1_tarski(X21)))) ),
    inference(subsumption_resolution,[],[f9050,f2161])).

fof(f9050,plain,(
    ! [X21] :
      ( v1_xboole_0(k1_tarski(X21))
      | ~ r2_hidden(X21,sK27(sK28(k1_tarski(X21)))) ) ),
    inference(resolution,[],[f8539,f2559])).

fof(f2559,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X2))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f2174,f2010])).

fof(f14651,plain,
    ( spl33_253
    | ~ spl33_4
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14646,f9474,f2259,f14648])).

fof(f14648,plain,
    ( spl33_253
  <=> r2_hidden(sK27(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_253])])).

fof(f14646,plain,
    ( r2_hidden(sK27(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_101 ),
    inference(forward_demodulation,[],[f14555,f2261])).

fof(f14555,plain,
    ( r2_hidden(sK27(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl33_101 ),
    inference(superposition,[],[f9079,f9476])).

fof(f14645,plain,
    ( spl33_252
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14554,f9474,f14642])).

fof(f14642,plain,
    ( spl33_252
  <=> m1_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_252])])).

fof(f14554,plain,
    ( m1_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl33_101 ),
    inference(superposition,[],[f8902,f9476])).

fof(f8902,plain,(
    ! [X8] : m1_subset_1(X8,sK28(k1_tarski(X8))) ),
    inference(superposition,[],[f2108,f8824])).

fof(f8824,plain,(
    ! [X20] : sK22(sK28(k1_tarski(X20))) = X20 ),
    inference(subsumption_resolution,[],[f8797,f2161])).

fof(f8797,plain,(
    ! [X20] :
      ( v1_xboole_0(k1_tarski(X20))
      | sK22(sK28(k1_tarski(X20))) = X20 ) ),
    inference(resolution,[],[f8327,f2238])).

fof(f14640,plain,
    ( spl33_243
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14550,f9474,f14595])).

fof(f14595,plain,
    ( spl33_243
  <=> k1_xboole_0 = sK22(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_243])])).

fof(f14550,plain,
    ( k1_xboole_0 = sK22(k1_xboole_0)
    | ~ spl33_101 ),
    inference(superposition,[],[f8824,f9476])).

fof(f14639,plain,
    ( ~ spl33_251
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14549,f9474,f14636])).

fof(f14636,plain,
    ( spl33_251
  <=> r2_hidden(k1_xboole_0,sK22(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_251])])).

fof(f14549,plain,
    ( ~ r2_hidden(k1_xboole_0,sK22(k1_xboole_0))
    | ~ spl33_101 ),
    inference(superposition,[],[f8823,f9476])).

fof(f8823,plain,(
    ! [X19] : ~ r2_hidden(X19,sK22(sK28(k1_tarski(X19)))) ),
    inference(subsumption_resolution,[],[f8796,f2161])).

fof(f8796,plain,(
    ! [X19] :
      ( v1_xboole_0(k1_tarski(X19))
      | ~ r2_hidden(X19,sK22(sK28(k1_tarski(X19)))) ) ),
    inference(resolution,[],[f8327,f2559])).

fof(f14634,plain,
    ( spl33_250
    | ~ spl33_4
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14629,f9474,f2259,f14631])).

fof(f14631,plain,
    ( spl33_250
  <=> r2_hidden(sK22(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_250])])).

fof(f14629,plain,
    ( r2_hidden(sK22(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_101 ),
    inference(forward_demodulation,[],[f14548,f2261])).

fof(f14548,plain,
    ( r2_hidden(sK22(k1_xboole_0),k1_zfmisc_1(k1_xboole_0))
    | ~ spl33_101 ),
    inference(superposition,[],[f8822,f9476])).

fof(f14628,plain,
    ( spl33_249
    | ~ spl33_97
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14544,f9474,f8661,f14625])).

fof(f8661,plain,
    ( spl33_97
  <=> k1_xboole_0 = sK27(sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_97])])).

fof(f14544,plain,
    ( k1_xboole_0 = sK27(k1_xboole_0)
    | ~ spl33_97
    | ~ spl33_101 ),
    inference(superposition,[],[f8663,f9476])).

fof(f8663,plain,
    ( k1_xboole_0 = sK27(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_97 ),
    inference(avatar_component_clause,[],[f8661])).

fof(f14623,plain,
    ( spl33_248
    | ~ spl33_96
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14542,f9474,f8581,f14620])).

fof(f14620,plain,
    ( spl33_248
  <=> v1_relat_1(sK27(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_248])])).

fof(f8581,plain,
    ( spl33_96
  <=> v1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_96])])).

fof(f14542,plain,
    ( v1_relat_1(sK27(k1_xboole_0))
    | ~ spl33_96
    | ~ spl33_101 ),
    inference(superposition,[],[f8583,f9476])).

fof(f8583,plain,
    ( v1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_96 ),
    inference(avatar_component_clause,[],[f8581])).

fof(f14618,plain,
    ( spl33_247
    | ~ spl33_95
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14541,f9474,f8575,f14615])).

fof(f14615,plain,
    ( spl33_247
  <=> r1_tarski(sK27(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_247])])).

fof(f14541,plain,
    ( r1_tarski(sK27(k1_xboole_0),k1_xboole_0)
    | ~ spl33_95
    | ~ spl33_101 ),
    inference(superposition,[],[f8577,f9476])).

fof(f14613,plain,
    ( spl33_246
    | ~ spl33_94
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14540,f9474,f8569,f14610])).

fof(f14610,plain,
    ( spl33_246
  <=> v1_xboole_0(sK27(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_246])])).

fof(f8569,plain,
    ( spl33_94
  <=> v1_xboole_0(sK27(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_94])])).

fof(f14540,plain,
    ( v1_xboole_0(sK27(k1_xboole_0))
    | ~ spl33_94
    | ~ spl33_101 ),
    inference(superposition,[],[f8571,f9476])).

fof(f8571,plain,
    ( v1_xboole_0(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_94 ),
    inference(avatar_component_clause,[],[f8569])).

fof(f14608,plain,
    ( spl33_245
    | ~ spl33_93
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14539,f9474,f8563,f14605])).

fof(f14605,plain,
    ( spl33_245
  <=> v1_relat_1(k1_relat_1(sK27(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_245])])).

fof(f8563,plain,
    ( spl33_93
  <=> v1_relat_1(k1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_93])])).

fof(f14539,plain,
    ( v1_relat_1(k1_relat_1(sK27(k1_xboole_0)))
    | ~ spl33_93
    | ~ spl33_101 ),
    inference(superposition,[],[f8565,f9476])).

fof(f8565,plain,
    ( v1_relat_1(k1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_93 ),
    inference(avatar_component_clause,[],[f8563])).

fof(f14603,plain,
    ( spl33_244
    | ~ spl33_92
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14538,f9474,f8556,f14600])).

fof(f14600,plain,
    ( spl33_244
  <=> v1_funct_1(sK27(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_244])])).

fof(f8556,plain,
    ( spl33_92
  <=> v1_funct_1(sK27(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_92])])).

fof(f14538,plain,
    ( v1_funct_1(sK27(k1_xboole_0))
    | ~ spl33_92
    | ~ spl33_101 ),
    inference(superposition,[],[f8558,f9476])).

fof(f8558,plain,
    ( v1_funct_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_92 ),
    inference(avatar_component_clause,[],[f8556])).

fof(f14598,plain,
    ( spl33_243
    | ~ spl33_91
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14537,f9474,f8478,f14595])).

fof(f8478,plain,
    ( spl33_91
  <=> k1_xboole_0 = sK22(sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_91])])).

fof(f14537,plain,
    ( k1_xboole_0 = sK22(k1_xboole_0)
    | ~ spl33_91
    | ~ spl33_101 ),
    inference(superposition,[],[f8480,f9476])).

fof(f8480,plain,
    ( k1_xboole_0 = sK22(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_91 ),
    inference(avatar_component_clause,[],[f8478])).

fof(f14593,plain,
    ( spl33_242
    | ~ spl33_90
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14535,f9474,f8363,f14590])).

fof(f14590,plain,
    ( spl33_242
  <=> v1_relat_1(sK22(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_242])])).

fof(f8363,plain,
    ( spl33_90
  <=> v1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_90])])).

fof(f14535,plain,
    ( v1_relat_1(sK22(k1_xboole_0))
    | ~ spl33_90
    | ~ spl33_101 ),
    inference(superposition,[],[f8365,f9476])).

fof(f8365,plain,
    ( v1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_90 ),
    inference(avatar_component_clause,[],[f8363])).

fof(f14588,plain,
    ( spl33_241
    | ~ spl33_89
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14534,f9474,f8357,f14585])).

fof(f14585,plain,
    ( spl33_241
  <=> r1_tarski(sK22(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_241])])).

fof(f14534,plain,
    ( r1_tarski(sK22(k1_xboole_0),k1_xboole_0)
    | ~ spl33_89
    | ~ spl33_101 ),
    inference(superposition,[],[f8359,f9476])).

fof(f14583,plain,
    ( spl33_240
    | ~ spl33_88
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14533,f9474,f8351,f14580])).

fof(f14580,plain,
    ( spl33_240
  <=> v1_xboole_0(sK22(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_240])])).

fof(f8351,plain,
    ( spl33_88
  <=> v1_xboole_0(sK22(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_88])])).

fof(f14533,plain,
    ( v1_xboole_0(sK22(k1_xboole_0))
    | ~ spl33_88
    | ~ spl33_101 ),
    inference(superposition,[],[f8353,f9476])).

fof(f8353,plain,
    ( v1_xboole_0(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_88 ),
    inference(avatar_component_clause,[],[f8351])).

fof(f14578,plain,
    ( spl33_239
    | ~ spl33_87
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14532,f9474,f8345,f14575])).

fof(f14575,plain,
    ( spl33_239
  <=> v1_relat_1(k1_relat_1(sK22(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_239])])).

fof(f8345,plain,
    ( spl33_87
  <=> v1_relat_1(k1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_87])])).

fof(f14532,plain,
    ( v1_relat_1(k1_relat_1(sK22(k1_xboole_0)))
    | ~ spl33_87
    | ~ spl33_101 ),
    inference(superposition,[],[f8347,f9476])).

fof(f8347,plain,
    ( v1_relat_1(k1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_87 ),
    inference(avatar_component_clause,[],[f8345])).

fof(f14488,plain,
    ( ~ spl33_4
    | ~ spl33_34
    | ~ spl33_43
    | ~ spl33_44 ),
    inference(avatar_contradiction_clause,[],[f14487])).

fof(f14487,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_34
    | ~ spl33_43
    | ~ spl33_44 ),
    inference(subsumption_resolution,[],[f14486,f2734])).

fof(f2734,plain,
    ( v1_relat_1(k1_tarski(k1_xboole_0))
    | ~ spl33_34 ),
    inference(avatar_component_clause,[],[f2732])).

fof(f14486,plain,
    ( ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_43
    | ~ spl33_44 ),
    inference(subsumption_resolution,[],[f14484,f3154])).

fof(f14484,plain,
    ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_43 ),
    inference(superposition,[],[f3150,f2261])).

fof(f14472,plain,
    ( ~ spl33_4
    | ~ spl33_33
    | ~ spl33_34 ),
    inference(avatar_contradiction_clause,[],[f14471])).

fof(f14471,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_33
    | ~ spl33_34 ),
    inference(subsumption_resolution,[],[f14469,f2734])).

fof(f14469,plain,
    ( ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_33 ),
    inference(superposition,[],[f2730,f2261])).

fof(f14444,plain,
    ( ~ spl33_47
    | spl33_75
    | ~ spl33_101 ),
    inference(avatar_split_clause,[],[f14443,f9474,f6847,f3401])).

fof(f6847,plain,
    ( spl33_75
  <=> k1_tarski(k1_xboole_0) = sK28(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_75])])).

fof(f14443,plain,
    ( k1_xboole_0 != k1_tarski(k1_xboole_0)
    | spl33_75
    | ~ spl33_101 ),
    inference(forward_demodulation,[],[f6848,f9476])).

fof(f6848,plain,
    ( k1_tarski(k1_xboole_0) != sK28(k1_tarski(k1_xboole_0))
    | spl33_75 ),
    inference(avatar_component_clause,[],[f6847])).

fof(f14440,plain,
    ( spl33_34
    | spl33_238
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f10942,f2259,f14438,f2732])).

fof(f14438,plain,
    ( spl33_238
  <=> ! [X22] :
        ( k1_xboole_0 = k1_tarski(X22)
        | ~ v1_xboole_0(X22)
        | ~ v1_relat_1(k1_tarski(X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_238])])).

fof(f10942,plain,
    ( ! [X22] :
        ( k1_xboole_0 = k1_tarski(X22)
        | v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(X22))
        | ~ v1_xboole_0(X22) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3432,f5507])).

fof(f5507,plain,
    ( ! [X9] :
        ( m1_subset_1(k1_xboole_0,k1_tarski(X9))
        | ~ v1_xboole_0(X9) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2078,f2424])).

fof(f2424,plain,
    ( ! [X0] :
        ( k1_tarski(X0) = k1_zfmisc_1(X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2261,f2152])).

fof(f14436,plain,
    ( spl33_237
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12022,f2259,f14433])).

fof(f14433,plain,
    ( spl33_237
  <=> v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_237])])).

fof(f12022,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12003,f2261])).

fof(f12003,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f9698,f7349])).

fof(f14431,plain,
    ( spl33_236
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12026,f2289,f2259,f14428])).

fof(f14428,plain,
    ( spl33_236
  <=> v1_xboole_0(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_236])])).

fof(f12026,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(forward_demodulation,[],[f12004,f2261])).

fof(f12004,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,sK28(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f9698,f6277])).

fof(f14426,plain,
    ( spl33_235
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12029,f2259,f14423])).

fof(f14423,plain,
    ( spl33_235
  <=> v1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_235])])).

fof(f12029,plain,
    ( v1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12005,f2261])).

fof(f12005,plain,(
    v1_relat_1(k5_setfam_1(k1_xboole_0,sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(resolution,[],[f9698,f3351])).

fof(f14421,plain,
    ( spl33_234
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12034,f2259,f14418])).

fof(f14418,plain,
    ( spl33_234
  <=> k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_234])])).

fof(f12034,plain,
    ( k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12007,f2261])).

fof(f12007,plain,(
    k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK28(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f9698,f2075])).

fof(f14416,plain,
    ( spl33_233
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12168,f2259,f14413])).

fof(f14413,plain,
    ( spl33_233
  <=> m1_subset_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_233])])).

fof(f12168,plain,
    ( m1_subset_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(superposition,[],[f9867,f2261])).

fof(f14411,plain,
    ( spl33_232
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12220,f2259,f14408])).

fof(f14408,plain,
    ( spl33_232
  <=> v1_relat_1(k1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_232])])).

fof(f12220,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12201,f2261])).

fof(f12201,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f12147,f7349])).

fof(f14406,plain,
    ( spl33_228
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12224,f2289,f2259,f14385])).

fof(f14385,plain,
    ( spl33_228
  <=> v1_xboole_0(k3_tarski(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_228])])).

fof(f12224,plain,
    ( v1_xboole_0(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(forward_demodulation,[],[f12202,f2261])).

fof(f12202,plain,
    ( v1_xboole_0(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f12147,f6277])).

fof(f14405,plain,
    ( spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12227,f2259,f14375])).

fof(f14375,plain,
    ( spl33_227
  <=> v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_227])])).

fof(f12227,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12203,f2261])).

fof(f12203,plain,(
    v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(resolution,[],[f12147,f3351])).

fof(f14404,plain,
    ( spl33_231
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12232,f2259,f14401])).

fof(f14401,plain,
    ( spl33_231
  <=> k1_xboole_0 = k3_tarski(sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_231])])).

fof(f12232,plain,
    ( k1_xboole_0 = k3_tarski(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12205,f2261])).

fof(f12205,plain,(
    k1_xboole_0 = k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f12147,f2075])).

fof(f14399,plain,
    ( ~ spl33_230
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12283,f2259,f14396])).

fof(f14396,plain,
    ( spl33_230
  <=> r2_hidden(k1_xboole_0,k3_tarski(sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_230])])).

fof(f12283,plain,
    ( ~ r2_hidden(k1_xboole_0,k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(superposition,[],[f12190,f2261])).

fof(f12190,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(sK28(k1_zfmisc_1(X0)))) ),
    inference(resolution,[],[f12147,f2010])).

fof(f14394,plain,
    ( ~ spl33_229
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12729,f2259,f14391])).

fof(f14391,plain,
    ( spl33_229
  <=> r2_hidden(k1_xboole_0,k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_229])])).

fof(f12729,plain,
    ( ~ r2_hidden(k1_xboole_0,k5_setfam_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(superposition,[],[f11992,f2261])).

fof(f11992,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_setfam_1(X0,sK28(k1_zfmisc_1(X0)))) ),
    inference(resolution,[],[f9698,f2010])).

fof(f14389,plain,
    ( spl33_227
    | ~ spl33_4
    | ~ spl33_16 ),
    inference(avatar_split_clause,[],[f12911,f2324,f2259,f14375])).

fof(f12911,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_16 ),
    inference(subsumption_resolution,[],[f12908,f2326])).

fof(f12908,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f12149,f2261])).

fof(f12149,plain,(
    ! [X6] :
      ( v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(X6))))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f9867,f2110])).

fof(f14388,plain,
    ( spl33_228
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12921,f2289,f2259,f14385])).

fof(f12921,plain,
    ( v1_xboole_0(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f12917,f2291])).

fof(f12917,plain,
    ( v1_xboole_0(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f12151,f2261])).

fof(f12151,plain,(
    ! [X9] :
      ( v1_xboole_0(k3_tarski(sK28(k1_zfmisc_1(X9))))
      | ~ v1_xboole_0(X9) ) ),
    inference(resolution,[],[f9867,f2149])).

fof(f14383,plain,
    ( spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12984,f2259,f14375])).

fof(f12984,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12974,f2261])).

fof(f12974,plain,(
    v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(superposition,[],[f12154,f2228])).

fof(f12154,plain,(
    ! [X17,X18] : v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k2_zfmisc_1(X17,X18))))) ),
    inference(resolution,[],[f9867,f2105])).

fof(f14382,plain,
    ( spl33_56
    | spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12987,f2259,f14375,f4925])).

fof(f12987,plain,
    ( ! [X2] :
        ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
        | ~ v1_xboole_0(X2) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12975,f2261])).

fof(f12975,plain,(
    ! [X2] :
      ( v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0))))
      | ~ v1_xboole_0(X2) ) ),
    inference(superposition,[],[f12154,f3740])).

fof(f3740,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 = k2_zfmisc_1(X13,X12)
      | ~ v1_xboole_0(X12) ) ),
    inference(resolution,[],[f3300,f2066])).

fof(f3300,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(X12,k2_zfmisc_1(X14,X13))
      | ~ v1_xboole_0(X13) ) ),
    inference(subsumption_resolution,[],[f3289,f2161])).

fof(f3289,plain,(
    ! [X14,X12,X13] :
      ( v1_xboole_0(k1_tarski(X12))
      | ~ v1_xboole_0(X13)
      | ~ r2_hidden(X12,k2_zfmisc_1(X14,X13)) ) ),
    inference(resolution,[],[f2134,f2194])).

fof(f2134,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1846])).

fof(f1846,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1213])).

fof(f1213,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f14381,plain,
    ( spl33_56
    | spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12990,f2259,f14375,f4925])).

fof(f12990,plain,
    ( ! [X3] :
        ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
        | ~ v1_xboole_0(X3) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12976,f2261])).

fof(f12976,plain,(
    ! [X3] :
      ( v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0))))
      | ~ v1_xboole_0(X3) ) ),
    inference(superposition,[],[f12154,f3714])).

fof(f3714,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 = k2_zfmisc_1(X12,X13)
      | ~ v1_xboole_0(X12) ) ),
    inference(resolution,[],[f3269,f2066])).

fof(f3269,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(X12,k2_zfmisc_1(X13,X14))
      | ~ v1_xboole_0(X13) ) ),
    inference(subsumption_resolution,[],[f3259,f2161])).

fof(f3259,plain,(
    ! [X14,X12,X13] :
      ( v1_xboole_0(k1_tarski(X12))
      | ~ v1_xboole_0(X13)
      | ~ r2_hidden(X12,k2_zfmisc_1(X13,X14)) ) ),
    inference(resolution,[],[f2133,f2194])).

fof(f2133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1845])).

fof(f1845,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1212])).

fof(f1212,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f14380,plain,
    ( spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12993,f2259,f14375])).

fof(f12993,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12979,f2261])).

fof(f12979,plain,(
    v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(superposition,[],[f12154,f9772])).

fof(f9772,plain,(
    ! [X21] : k1_xboole_0 = k2_zfmisc_1(X21,k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f9746,f3170])).

fof(f3170,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = k2_zfmisc_1(X1,X0) ) ),
    inference(resolution,[],[f2115,f2058])).

fof(f2058,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f1804])).

fof(f2115,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1834])).

fof(f14379,plain,
    ( spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12996,f2259,f14375])).

fof(f12996,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12980,f2261])).

fof(f12980,plain,(
    v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(superposition,[],[f12154,f2229])).

fof(f14378,plain,
    ( spl33_227
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12999,f2259,f14375])).

fof(f12999,plain,
    ( v1_relat_1(k3_tarski(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f12981,f2261])).

fof(f12981,plain,(
    v1_relat_1(k3_tarski(sK28(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(superposition,[],[f12154,f9770])).

fof(f9770,plain,(
    ! [X20] : k1_xboole_0 = k2_zfmisc_1(k3_tarski(k1_xboole_0),X20) ),
    inference(resolution,[],[f9746,f3160])).

fof(f3160,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X0,X1))
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(resolution,[],[f2114,f2057])).

fof(f14373,plain,
    ( spl33_226
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13022,f2259,f14370])).

fof(f14370,plain,
    ( spl33_226
  <=> r2_hidden(k3_tarski(sK28(k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_226])])).

fof(f13022,plain,
    ( r2_hidden(k3_tarski(sK28(k1_tarski(k1_xboole_0))),k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(superposition,[],[f12170,f2261])).

fof(f14368,plain,
    ( spl33_43
    | spl33_216 ),
    inference(avatar_split_clause,[],[f5480,f14322,f3149])).

fof(f14367,plain,
    ( spl33_44
    | spl33_225
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f9191,f2259,f14365,f3152])).

fof(f14365,plain,
    ( spl33_225
  <=> ! [X9] :
        ( ~ v1_funct_1(k1_tarski(X9))
        | ~ v1_xboole_0(X9)
        | ~ v1_relat_1(k1_tarski(X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_225])])).

fof(f9191,plain,
    ( ! [X9] :
        ( ~ v1_funct_1(k1_tarski(X9))
        | ~ v1_relat_1(k1_tarski(X9))
        | v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X9) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3141,f5537])).

fof(f5537,plain,
    ( ! [X58] :
        ( r2_hidden(k1_xboole_0,k1_tarski(X58))
        | ~ v1_xboole_0(X58) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2548,f2424])).

fof(f14363,plain,
    ( ~ spl33_34
    | spl33_224
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f7634,f2259,f14361,f2732])).

fof(f14361,plain,
    ( spl33_224
  <=> ! [X11] :
        ( ~ r1_tarski(X11,k1_xboole_0)
        | v1_relat_1(k1_zfmisc_1(X11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_224])])).

fof(f7634,plain,
    ( ! [X11] :
        ( ~ r1_tarski(X11,k1_xboole_0)
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | v1_relat_1(k1_zfmisc_1(X11)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2742,f2716])).

fof(f2742,plain,
    ( ! [X0] :
        ( r1_tarski(k1_zfmisc_1(X0),k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X0,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2111,f2261])).

fof(f2111,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1829])).

fof(f1829,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f432])).

fof(f432,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f14359,plain,
    ( spl33_223
    | ~ spl33_34
    | ~ spl33_44
    | ~ spl33_72 ),
    inference(avatar_split_clause,[],[f8409,f6653,f3152,f2732,f14356])).

fof(f14356,plain,
    ( spl33_223
  <=> v1_funct_1(sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_223])])).

fof(f8409,plain,
    ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
    | ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | v1_funct_1(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_72 ),
    inference(resolution,[],[f3134,f6655])).

fof(f14354,plain,
    ( spl33_222
    | ~ spl33_34
    | ~ spl33_44
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8410,f2259,f3152,f2732,f14352])).

fof(f14352,plain,
    ( spl33_222
  <=> ! [X58] :
        ( v1_funct_1(k1_zfmisc_1(X58))
        | ~ r1_tarski(X58,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_222])])).

fof(f8410,plain,
    ( ! [X58] :
        ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | v1_funct_1(k1_zfmisc_1(X58))
        | ~ r1_tarski(X58,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3134,f2742])).

fof(f14350,plain,
    ( spl33_221
    | ~ spl33_34
    | ~ spl33_44
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f9185,f2259,f3152,f2732,f14348])).

fof(f9185,plain,
    ( ! [X1] :
        ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | v1_funct_1(k1_tarski(X1))
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3141,f2578])).

fof(f14346,plain,
    ( spl33_216
    | ~ spl33_34
    | ~ spl33_44
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f9186,f2259,f3152,f2732,f14322])).

fof(f9186,plain,
    ( ! [X2] :
        ( ~ v1_funct_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | v1_funct_1(k1_tarski(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3141,f2688])).

fof(f2688,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2556,f2261])).

fof(f2556,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2548,f2152])).

fof(f14345,plain,
    ( ~ spl33_34
    | spl33_79
    | spl33_47
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f10931,f2259,f3401,f6871,f2732])).

fof(f6871,plain,
    ( spl33_79
  <=> ! [X1] :
        ( v1_relat_1(k1_tarski(X1))
        | ~ r1_tarski(X1,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_79])])).

fof(f10931,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_tarski(X3))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X3,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3432,f2479])).

fof(f14344,plain,
    ( ~ spl33_34
    | spl33_78
    | spl33_47
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f10932,f2259,f3401,f6866,f2732])).

fof(f6866,plain,
    ( spl33_78
  <=> ! [X4] :
        ( v1_relat_1(k1_tarski(X4))
        | ~ v1_xboole_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_78])])).

fof(f10932,plain,
    ( ! [X4] :
        ( k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_tarski(X4))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X4) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3432,f2450])).

fof(f14342,plain,
    ( ~ spl33_34
    | spl33_47
    | spl33_220
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12179,f2259,f14340,f3401,f2732])).

fof(f14340,plain,
    ( spl33_220
  <=> ! [X13,X14] :
        ( ~ m1_subset_1(X13,k1_tarski(k1_xboole_0))
        | v1_relat_1(k1_tarski(k9_subset_1(k1_xboole_0,X14,X13))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_220])])).

fof(f12179,plain,
    ( ! [X14,X13] :
        ( ~ m1_subset_1(X13,k1_tarski(k1_xboole_0))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_tarski(k9_subset_1(k1_xboole_0,X14,X13)))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3549,f3432])).

fof(f14338,plain,
    ( ~ spl33_34
    | spl33_47
    | spl33_219
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12317,f2259,f14336,f3401,f2732])).

fof(f14336,plain,
    ( spl33_219
  <=> ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_tarski(k1_xboole_0)))
        | v1_relat_1(k1_tarski(k5_setfam_1(k1_xboole_0,X7))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_219])])).

fof(f12317,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k1_tarski(k1_xboole_0)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_tarski(k5_setfam_1(k1_xboole_0,X7)))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3571,f3432])).

fof(f14334,plain,
    ( spl33_218
    | spl33_34 ),
    inference(avatar_split_clause,[],[f7190,f2732,f14332])).

fof(f14332,plain,
    ( spl33_218
  <=> ! [X70] :
        ( ~ v1_relat_1(k1_zfmisc_1(sK26(X70)))
        | ~ v1_xboole_0(X70) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_218])])).

fof(f7190,plain,(
    ! [X70] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(sK26(X70)))
      | ~ v1_xboole_0(X70) ) ),
    inference(superposition,[],[f6402,f6984])).

fof(f6984,plain,(
    ! [X21] :
      ( k1_xboole_0 = sK26(sK26(X21))
      | ~ v1_xboole_0(X21) ) ),
    inference(resolution,[],[f6765,f2066])).

fof(f6765,plain,(
    ! [X28,X27] :
      ( ~ r2_hidden(X27,sK26(sK26(X28)))
      | ~ v1_xboole_0(X28) ) ),
    inference(resolution,[],[f2983,f3857])).

fof(f2983,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2125,f2107])).

fof(f2125,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1836])).

fof(f1836,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f629])).

fof(f629,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f6402,plain,(
    ! [X40] :
      ( v1_relat_1(k1_tarski(sK26(X40)))
      | ~ v1_relat_1(k1_zfmisc_1(X40)) ) ),
    inference(resolution,[],[f2821,f2768])).

fof(f2821,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | v1_relat_1(k1_tarski(X2))
      | ~ v1_relat_1(X3) ) ),
    inference(resolution,[],[f2194,f2110])).

fof(f14330,plain,
    ( spl33_217
    | spl33_34 ),
    inference(avatar_split_clause,[],[f8206,f2732,f14328])).

fof(f14328,plain,
    ( spl33_217
  <=> ! [X59] :
        ( ~ v1_relat_1(k1_zfmisc_1(k1_relat_1(X59)))
        | ~ v1_xboole_0(X59) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_217])])).

fof(f8206,plain,(
    ! [X59] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(k1_relat_1(X59)))
      | ~ v1_xboole_0(X59) ) ),
    inference(superposition,[],[f6402,f7951])).

fof(f7951,plain,(
    ! [X26] :
      ( k1_xboole_0 = sK26(k1_relat_1(X26))
      | ~ v1_xboole_0(X26) ) ),
    inference(resolution,[],[f7834,f2075])).

fof(f7834,plain,(
    ! [X8,X7] :
      ( r1_tarski(sK26(k1_relat_1(X8)),X7)
      | ~ v1_xboole_0(X8) ) ),
    inference(superposition,[],[f7782,f2354])).

fof(f14326,plain,
    ( spl33_44
    | spl33_43 ),
    inference(avatar_split_clause,[],[f8412,f3149,f3152])).

fof(f8412,plain,(
    ! [X60] :
      ( ~ v1_funct_1(k1_zfmisc_1(X60))
      | ~ v1_relat_1(k1_zfmisc_1(X60))
      | v1_funct_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f3134,f2465])).

fof(f14325,plain,
    ( spl33_216
    | spl33_43 ),
    inference(avatar_split_clause,[],[f8413,f3149,f14322])).

fof(f8413,plain,(
    ! [X61,X62] :
      ( ~ v1_funct_1(k1_zfmisc_1(X61))
      | ~ v1_relat_1(k1_zfmisc_1(X61))
      | v1_funct_1(k1_tarski(X62))
      | ~ v1_xboole_0(X62) ) ),
    inference(resolution,[],[f3134,f2481])).

fof(f2481,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2465,f2152])).

fof(f14324,plain,
    ( spl33_216
    | spl33_43 ),
    inference(avatar_split_clause,[],[f9188,f3149,f14322])).

fof(f9188,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(k1_zfmisc_1(X4))
      | ~ v1_relat_1(k1_zfmisc_1(X4))
      | v1_funct_1(k1_tarski(X5))
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f3141,f2556])).

fof(f14320,plain,
    ( spl33_44
    | spl33_43 ),
    inference(avatar_split_clause,[],[f9190,f3149,f3152])).

fof(f9190,plain,(
    ! [X8] :
      ( ~ v1_funct_1(k1_zfmisc_1(X8))
      | ~ v1_relat_1(k1_zfmisc_1(X8))
      | v1_funct_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f3141,f2548])).

fof(f14319,plain,
    ( spl33_215
    | spl33_214 ),
    inference(avatar_split_clause,[],[f9192,f14312,f14316])).

fof(f14316,plain,
    ( spl33_215
  <=> v1_funct_1(k1_tarski(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_215])])).

fof(f14312,plain,
    ( spl33_214
  <=> ! [X13] :
        ( ~ v1_funct_1(k1_zfmisc_1(k1_zfmisc_1(X13)))
        | ~ v1_relat_1(k1_zfmisc_1(k1_zfmisc_1(X13))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_214])])).

fof(f9192,plain,(
    ! [X10] :
      ( ~ v1_funct_1(k1_zfmisc_1(k1_zfmisc_1(X10)))
      | ~ v1_relat_1(k1_zfmisc_1(k1_zfmisc_1(X10)))
      | v1_funct_1(k1_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f3141,f2767])).

fof(f14314,plain,
    ( spl33_213
    | spl33_214 ),
    inference(avatar_split_clause,[],[f9194,f14312,f14309])).

fof(f14309,plain,
    ( spl33_213
  <=> ! [X14] :
        ( v1_funct_1(k1_tarski(k1_tarski(X14)))
        | ~ v1_xboole_0(X14) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_213])])).

fof(f9194,plain,(
    ! [X14,X13] :
      ( ~ v1_funct_1(k1_zfmisc_1(k1_zfmisc_1(X13)))
      | ~ v1_relat_1(k1_zfmisc_1(k1_zfmisc_1(X13)))
      | v1_funct_1(k1_tarski(k1_tarski(X14)))
      | ~ v1_xboole_0(X14) ) ),
    inference(resolution,[],[f3141,f2818])).

fof(f2818,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_tarski(X0),k1_zfmisc_1(k1_zfmisc_1(X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2767,f2152])).

fof(f14307,plain,
    ( spl33_33
    | spl33_78 ),
    inference(avatar_split_clause,[],[f14306,f6866,f2729])).

fof(f14306,plain,(
    ! [X8,X9] :
      ( v1_relat_1(k1_tarski(X9))
      | ~ v1_relat_1(k1_zfmisc_1(X8))
      | ~ v1_xboole_0(X9) ) ),
    inference(global_subsumption,[],[f3815])).

fof(f3815,plain,(
    ! [X8,X7] :
      ( ~ v1_xboole_0(X7)
      | ~ v1_relat_1(k1_zfmisc_1(X8))
      | v1_relat_1(k1_tarski(X7)) ) ),
    inference(resolution,[],[f2481,f2716])).

fof(f14305,plain,
    ( spl33_79
    | spl33_212 ),
    inference(avatar_split_clause,[],[f10936,f14300,f6871])).

fof(f14300,plain,
    ( spl33_212
  <=> ! [X20,X21] :
        ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X20,X21))
        | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_212])])).

fof(f10936,plain,(
    ! [X12,X10,X11] :
      ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X10,X11))
      | v1_relat_1(k1_tarski(X12))
      | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ r1_tarski(X12,k1_xboole_0) ) ),
    inference(resolution,[],[f3432,f4685])).

fof(f14304,plain,
    ( spl33_33
    | spl33_34 ),
    inference(avatar_split_clause,[],[f14303,f2732,f2729])).

fof(f14303,plain,(
    ! [X19] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(X19)) ) ),
    inference(global_subsumption,[],[f3462])).

fof(f3462,plain,(
    ! [X20] :
      ( ~ v1_relat_1(k1_zfmisc_1(X20))
      | v1_relat_1(k1_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f2716,f2465])).

fof(f14302,plain,
    ( spl33_34
    | spl33_212 ),
    inference(avatar_split_clause,[],[f10941,f14300,f2732])).

fof(f10941,plain,(
    ! [X21,X20] :
      ( k1_xboole_0 = k1_zfmisc_1(k2_zfmisc_1(X20,X21))
      | v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(k2_zfmisc_1(X20,X21))) ) ),
    inference(resolution,[],[f3432,f2065])).

fof(f14298,plain,
    ( spl33_211
    | spl33_34
    | ~ spl33_121 ),
    inference(avatar_split_clause,[],[f14294,f10100,f2732,f14296])).

fof(f14296,plain,
    ( spl33_211
  <=> ! [X30] :
        ( k1_xboole_0 = k1_zfmisc_1(X30)
        | ~ v1_relat_1(k1_zfmisc_1(X30)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_211])])).

fof(f14294,plain,
    ( ! [X30] :
        ( v1_relat_1(k1_tarski(k1_xboole_0))
        | k1_xboole_0 = k1_zfmisc_1(X30)
        | ~ v1_relat_1(k1_zfmisc_1(X30)) )
    | ~ spl33_121 ),
    inference(forward_demodulation,[],[f10948,f10102])).

fof(f10948,plain,(
    ! [X30] :
      ( k1_xboole_0 = k1_zfmisc_1(X30)
      | v1_relat_1(k1_tarski(k3_tarski(k1_tarski(k1_xboole_0))))
      | ~ v1_relat_1(k1_zfmisc_1(X30)) ) ),
    inference(resolution,[],[f3432,f9833])).

fof(f9833,plain,(
    ! [X8] : m1_subset_1(k3_tarski(k1_tarski(k1_xboole_0)),k1_zfmisc_1(X8)) ),
    inference(resolution,[],[f3576,f2077])).

fof(f14293,plain,
    ( spl33_33
    | spl33_210 ),
    inference(avatar_split_clause,[],[f14292,f14289,f2729])).

fof(f14289,plain,
    ( spl33_210
  <=> ! [X29] :
        ( ~ v1_xboole_0(X29)
        | v1_relat_1(k1_tarski(k3_tarski(X29))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_210])])).

fof(f14292,plain,(
    ! [X47,X46] :
      ( ~ v1_xboole_0(X46)
      | v1_relat_1(k1_tarski(k3_tarski(X46)))
      | ~ v1_relat_1(k1_zfmisc_1(X47)) ) ),
    inference(global_subsumption,[],[f12780])).

fof(f12780,plain,(
    ! [X30,X29] :
      ( ~ v1_xboole_0(X29)
      | v1_relat_1(k1_tarski(k3_tarski(X29)))
      | ~ v1_relat_1(k1_zfmisc_1(X30)) ) ),
    inference(resolution,[],[f12090,f2821])).

fof(f14291,plain,
    ( spl33_33
    | spl33_210 ),
    inference(avatar_split_clause,[],[f12780,f14289,f2729])).

fof(f14287,plain,
    ( spl33_43
    | spl33_209 ),
    inference(avatar_split_clause,[],[f12781,f14285,f3149])).

fof(f14232,plain,
    ( spl33_207
    | spl33_208
    | ~ spl33_71 ),
    inference(avatar_split_clause,[],[f13756,f6411,f14230,f14226])).

fof(f14226,plain,
    ( spl33_207
  <=> k1_xboole_0 = k1_tarski(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_207])])).

fof(f14230,plain,
    ( spl33_208
  <=> ! [X380] :
        ( v1_relat_1(k1_tarski(X380))
        | ~ r2_hidden(k1_tarski(k1_xboole_0),k1_tarski(X380)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_208])])).

fof(f13756,plain,
    ( ! [X380] :
        ( v1_relat_1(k1_tarski(X380))
        | k1_xboole_0 = k1_tarski(k1_tarski(k1_xboole_0))
        | ~ r2_hidden(k1_tarski(k1_xboole_0),k1_tarski(X380)) )
    | ~ spl33_71 ),
    inference(superposition,[],[f6413,f3423])).

fof(f3423,plain,(
    ! [X14,X13] :
      ( k1_tarski(X13) = k1_tarski(X14)
      | k1_xboole_0 = k1_tarski(X13)
      | ~ r2_hidden(X13,k1_tarski(X14)) ) ),
    inference(resolution,[],[f2051,f2174])).

fof(f2051,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f1946])).

fof(f14224,plain,
    ( spl33_47
    | spl33_206
    | ~ spl33_121 ),
    inference(avatar_split_clause,[],[f13753,f10100,f14222,f3401])).

fof(f14222,plain,
    ( spl33_206
  <=> ! [X375] :
        ( k1_xboole_0 = k3_tarski(k1_tarski(X375))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X375)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_206])])).

fof(f13753,plain,
    ( ! [X375] :
        ( k1_xboole_0 = k3_tarski(k1_tarski(X375))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X375)) )
    | ~ spl33_121 ),
    inference(superposition,[],[f10102,f3423])).

fof(f14220,plain,
    ( spl33_47
    | spl33_205 ),
    inference(avatar_split_clause,[],[f13752,f14218,f3401])).

fof(f14218,plain,
    ( spl33_205
  <=> ! [X373,X374] :
        ( ~ r2_hidden(X374,k3_tarski(k1_tarski(X373)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X373)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_205])])).

fof(f13752,plain,(
    ! [X374,X373] :
      ( ~ r2_hidden(X374,k3_tarski(k1_tarski(X373)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X373)) ) ),
    inference(superposition,[],[f10046,f3423])).

fof(f14216,plain,
    ( spl33_47
    | spl33_204 ),
    inference(avatar_split_clause,[],[f13751,f14214,f3401])).

fof(f14214,plain,
    ( spl33_204
  <=> ! [X371,X372] :
        ( r1_tarski(k3_tarski(k1_tarski(X371)),X372)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X371)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_204])])).

fof(f13751,plain,(
    ! [X372,X371] :
      ( r1_tarski(k3_tarski(k1_tarski(X371)),X372)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X371)) ) ),
    inference(superposition,[],[f10041,f3423])).

fof(f14212,plain,
    ( spl33_47
    | spl33_203
    | ~ spl33_116 ),
    inference(avatar_split_clause,[],[f13750,f10037,f14210,f3401])).

fof(f14210,plain,
    ( spl33_203
  <=> ! [X370] :
        ( k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_tarski(X370))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X370)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_203])])).

fof(f10037,plain,
    ( spl33_116
  <=> k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_116])])).

fof(f13750,plain,
    ( ! [X370] :
        ( k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_tarski(X370))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X370)) )
    | ~ spl33_116 ),
    inference(superposition,[],[f10039,f3423])).

fof(f10039,plain,
    ( k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl33_116 ),
    inference(avatar_component_clause,[],[f10037])).

fof(f14208,plain,
    ( spl33_47
    | spl33_202 ),
    inference(avatar_split_clause,[],[f13749,f14206,f3401])).

fof(f14206,plain,
    ( spl33_202
  <=> ! [X369,X368] :
        ( r1_tarski(k5_setfam_1(sK26(X369),k1_tarski(X368)),X369)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X368)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_202])])).

fof(f13749,plain,(
    ! [X368,X369] :
      ( r1_tarski(k5_setfam_1(sK26(X369),k1_tarski(X368)),X369)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X368)) ) ),
    inference(superposition,[],[f10018,f3423])).

fof(f14204,plain,
    ( spl33_47
    | spl33_201 ),
    inference(avatar_split_clause,[],[f13748,f14202,f3401])).

fof(f14202,plain,
    ( spl33_201
  <=> ! [X367,X365,X366] :
        ( v1_relat_1(k5_setfam_1(k2_zfmisc_1(X366,X367),k1_tarski(X365)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X365)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_201])])).

fof(f13748,plain,(
    ! [X366,X365,X367] :
      ( v1_relat_1(k5_setfam_1(k2_zfmisc_1(X366,X367),k1_tarski(X365)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X365)) ) ),
    inference(superposition,[],[f10015,f3423])).

fof(f10015,plain,(
    ! [X24,X25] : v1_relat_1(k5_setfam_1(k2_zfmisc_1(X24,X25),k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f9665,f2689])).

fof(f14200,plain,
    ( spl33_47
    | spl33_200 ),
    inference(avatar_split_clause,[],[f13747,f14198,f3401])).

fof(f14198,plain,
    ( spl33_200
  <=> ! [X363,X364] :
        ( r1_tarski(k5_setfam_1(k1_xboole_0,k1_tarski(X363)),X364)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X363)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_200])])).

fof(f13747,plain,(
    ! [X364,X363] :
      ( r1_tarski(k5_setfam_1(k1_xboole_0,k1_tarski(X363)),X364)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X363)) ) ),
    inference(superposition,[],[f10008,f3423])).

fof(f14196,plain,
    ( spl33_47
    | spl33_199 ),
    inference(avatar_split_clause,[],[f13746,f14194,f3401])).

fof(f14194,plain,
    ( spl33_199
  <=> ! [X361,X362] :
        ( v1_relat_1(k5_setfam_1(X362,k1_tarski(X361)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X361))
        | ~ v1_xboole_0(X362) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_199])])).

fof(f13746,plain,(
    ! [X362,X361] :
      ( v1_relat_1(k5_setfam_1(X362,k1_tarski(X361)))
      | ~ v1_xboole_0(X362)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X361)) ) ),
    inference(superposition,[],[f10004,f3423])).

fof(f10004,plain,(
    ! [X14] :
      ( v1_relat_1(k5_setfam_1(X14,k1_tarski(k1_xboole_0)))
      | ~ v1_xboole_0(X14) ) ),
    inference(resolution,[],[f9665,f3352])).

fof(f14192,plain,
    ( spl33_47
    | spl33_198 ),
    inference(avatar_split_clause,[],[f13745,f14190,f3401])).

fof(f14190,plain,
    ( spl33_198
  <=> ! [X359,X360] :
        ( v1_xboole_0(k5_setfam_1(X360,k1_tarski(X359)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X359))
        | ~ v1_xboole_0(X360) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_198])])).

fof(f13745,plain,(
    ! [X360,X359] :
      ( v1_xboole_0(k5_setfam_1(X360,k1_tarski(X359)))
      | ~ v1_xboole_0(X360)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X359)) ) ),
    inference(superposition,[],[f10000,f3423])).

fof(f10000,plain,(
    ! [X8] :
      ( v1_xboole_0(k5_setfam_1(X8,k1_tarski(k1_xboole_0)))
      | ~ v1_xboole_0(X8) ) ),
    inference(resolution,[],[f9665,f2782])).

fof(f14188,plain,
    ( spl33_47
    | spl33_197 ),
    inference(avatar_split_clause,[],[f13744,f14186,f3401])).

fof(f14186,plain,
    ( spl33_197
  <=> ! [X357,X358] :
        ( v1_relat_1(k5_setfam_1(X358,k1_tarski(X357)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X357))
        | ~ v1_relat_1(X358) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_197])])).

fof(f13744,plain,(
    ! [X358,X357] :
      ( v1_relat_1(k5_setfam_1(X358,k1_tarski(X357)))
      | ~ v1_relat_1(X358)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X357)) ) ),
    inference(superposition,[],[f9999,f3423])).

fof(f9999,plain,(
    ! [X7] :
      ( v1_relat_1(k5_setfam_1(X7,k1_tarski(k1_xboole_0)))
      | ~ v1_relat_1(X7) ) ),
    inference(resolution,[],[f9665,f2716])).

fof(f14184,plain,
    ( spl33_47
    | spl33_196 ),
    inference(avatar_split_clause,[],[f13743,f14182,f3401])).

fof(f14182,plain,
    ( spl33_196
  <=> ! [X355,X356] :
        ( ~ r2_hidden(X356,k5_setfam_1(X356,k1_tarski(X355)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X355)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_196])])).

fof(f13743,plain,(
    ! [X356,X355] :
      ( ~ r2_hidden(X356,k5_setfam_1(X356,k1_tarski(X355)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X355)) ) ),
    inference(superposition,[],[f9994,f3423])).

fof(f9994,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_setfam_1(X0,k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f9665,f2010])).

fof(f14180,plain,
    ( spl33_47
    | spl33_195 ),
    inference(avatar_split_clause,[],[f13742,f14178,f3401])).

fof(f14178,plain,
    ( spl33_195
  <=> ! [X353,X354] :
        ( m1_subset_1(k3_tarski(k1_tarski(X353)),k1_zfmisc_1(X354))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X353)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_195])])).

fof(f13742,plain,(
    ! [X354,X353] :
      ( m1_subset_1(k3_tarski(k1_tarski(X353)),k1_zfmisc_1(X354))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X353)) ) ),
    inference(superposition,[],[f9833,f3423])).

fof(f14176,plain,
    ( spl33_47
    | spl33_194 ),
    inference(avatar_split_clause,[],[f13741,f14174,f3401])).

fof(f14174,plain,
    ( spl33_194
  <=> ! [X351,X352] :
        ( r1_tarski(k5_setfam_1(X352,k1_tarski(X351)),X352)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X351)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_194])])).

fof(f13741,plain,(
    ! [X352,X351] :
      ( r1_tarski(k5_setfam_1(X352,k1_tarski(X351)),X352)
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X351)) ) ),
    inference(superposition,[],[f9665,f3423])).

fof(f14171,plain,
    ( spl33_47
    | spl33_192
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f14170,f2259,f14153,f3401])).

fof(f14153,plain,
    ( spl33_192
  <=> ! [X340,X341] :
        ( r1_tarski(X340,X341)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X340)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_192])])).

fof(f14170,plain,
    ( ! [X349,X348] :
        ( r1_tarski(X348,X349)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X348)) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f13739,f9081])).

fof(f13739,plain,
    ( ! [X349,X348] :
        ( r1_tarski(sK27(sK28(k1_tarski(X348))),X349)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X348)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f8658,f3423])).

fof(f14169,plain,
    ( spl33_47
    | spl33_191
    | ~ spl33_96 ),
    inference(avatar_split_clause,[],[f14168,f8581,f14148,f3401])).

fof(f14148,plain,
    ( spl33_191
  <=> ! [X339] :
        ( v1_relat_1(X339)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X339)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_191])])).

fof(f14168,plain,
    ( ! [X347] :
        ( v1_relat_1(X347)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X347)) )
    | ~ spl33_96 ),
    inference(forward_demodulation,[],[f13738,f9081])).

fof(f13738,plain,
    ( ! [X347] :
        ( v1_relat_1(sK27(sK28(k1_tarski(X347))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X347)) )
    | ~ spl33_96 ),
    inference(superposition,[],[f8583,f3423])).

fof(f14167,plain,
    ( spl33_47
    | spl33_156
    | ~ spl33_95 ),
    inference(avatar_split_clause,[],[f14166,f8575,f14000,f3401])).

fof(f14000,plain,
    ( spl33_156
  <=> ! [X267] :
        ( r1_tarski(X267,k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X267)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_156])])).

fof(f14166,plain,
    ( ! [X346] :
        ( r1_tarski(X346,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X346)) )
    | ~ spl33_95 ),
    inference(forward_demodulation,[],[f13737,f9081])).

fof(f13737,plain,
    ( ! [X346] :
        ( r1_tarski(sK27(sK28(k1_tarski(X346))),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X346)) )
    | ~ spl33_95 ),
    inference(superposition,[],[f8577,f3423])).

fof(f14165,plain,
    ( spl33_47
    | spl33_190
    | ~ spl33_94 ),
    inference(avatar_split_clause,[],[f14164,f8569,f14141,f3401])).

fof(f14141,plain,
    ( spl33_190
  <=> ! [X337] :
        ( v1_xboole_0(X337)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X337)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_190])])).

fof(f14164,plain,
    ( ! [X345] :
        ( v1_xboole_0(X345)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X345)) )
    | ~ spl33_94 ),
    inference(forward_demodulation,[],[f13736,f9081])).

fof(f13736,plain,
    ( ! [X345] :
        ( v1_xboole_0(sK27(sK28(k1_tarski(X345))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X345)) )
    | ~ spl33_94 ),
    inference(superposition,[],[f8571,f3423])).

fof(f14163,plain,
    ( spl33_47
    | spl33_189
    | ~ spl33_93 ),
    inference(avatar_split_clause,[],[f14162,f8563,f14136,f3401])).

fof(f14136,plain,
    ( spl33_189
  <=> ! [X336] :
        ( v1_relat_1(k1_relat_1(X336))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X336)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_189])])).

fof(f14162,plain,
    ( ! [X344] :
        ( v1_relat_1(k1_relat_1(X344))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X344)) )
    | ~ spl33_93 ),
    inference(forward_demodulation,[],[f13735,f9081])).

fof(f13735,plain,
    ( ! [X344] :
        ( v1_relat_1(k1_relat_1(sK27(sK28(k1_tarski(X344)))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X344)) )
    | ~ spl33_93 ),
    inference(superposition,[],[f8565,f3423])).

fof(f14161,plain,
    ( spl33_47
    | spl33_193
    | ~ spl33_92 ),
    inference(avatar_split_clause,[],[f14157,f8556,f14159,f3401])).

fof(f14159,plain,
    ( spl33_193
  <=> ! [X343] :
        ( v1_funct_1(X343)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X343)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_193])])).

fof(f14157,plain,
    ( ! [X343] :
        ( v1_funct_1(X343)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X343)) )
    | ~ spl33_92 ),
    inference(forward_demodulation,[],[f13734,f9081])).

fof(f13734,plain,
    ( ! [X343] :
        ( v1_funct_1(sK27(sK28(k1_tarski(X343))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X343)) )
    | ~ spl33_92 ),
    inference(superposition,[],[f8558,f3423])).

fof(f14155,plain,
    ( spl33_47
    | spl33_192
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f14151,f2259,f14153,f3401])).

fof(f14151,plain,
    ( ! [X341,X340] :
        ( r1_tarski(X340,X341)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X340)) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f13732,f8824])).

fof(f13732,plain,
    ( ! [X341,X340] :
        ( r1_tarski(sK22(sK28(k1_tarski(X340))),X341)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X340)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f8475,f3423])).

fof(f14150,plain,
    ( spl33_47
    | spl33_191
    | ~ spl33_90 ),
    inference(avatar_split_clause,[],[f14146,f8363,f14148,f3401])).

fof(f14146,plain,
    ( ! [X339] :
        ( v1_relat_1(X339)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X339)) )
    | ~ spl33_90 ),
    inference(forward_demodulation,[],[f13731,f8824])).

fof(f13731,plain,
    ( ! [X339] :
        ( v1_relat_1(sK22(sK28(k1_tarski(X339))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X339)) )
    | ~ spl33_90 ),
    inference(superposition,[],[f8365,f3423])).

fof(f14145,plain,
    ( spl33_47
    | spl33_156
    | ~ spl33_89 ),
    inference(avatar_split_clause,[],[f14144,f8357,f14000,f3401])).

fof(f14144,plain,
    ( ! [X338] :
        ( r1_tarski(X338,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X338)) )
    | ~ spl33_89 ),
    inference(forward_demodulation,[],[f13730,f8824])).

fof(f13730,plain,
    ( ! [X338] :
        ( r1_tarski(sK22(sK28(k1_tarski(X338))),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X338)) )
    | ~ spl33_89 ),
    inference(superposition,[],[f8359,f3423])).

fof(f14143,plain,
    ( spl33_47
    | spl33_190
    | ~ spl33_88 ),
    inference(avatar_split_clause,[],[f14139,f8351,f14141,f3401])).

fof(f14139,plain,
    ( ! [X337] :
        ( v1_xboole_0(X337)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X337)) )
    | ~ spl33_88 ),
    inference(forward_demodulation,[],[f13729,f8824])).

fof(f13729,plain,
    ( ! [X337] :
        ( v1_xboole_0(sK22(sK28(k1_tarski(X337))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X337)) )
    | ~ spl33_88 ),
    inference(superposition,[],[f8353,f3423])).

fof(f14138,plain,
    ( spl33_47
    | spl33_189
    | ~ spl33_87 ),
    inference(avatar_split_clause,[],[f14134,f8345,f14136,f3401])).

fof(f14134,plain,
    ( ! [X336] :
        ( v1_relat_1(k1_relat_1(X336))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X336)) )
    | ~ spl33_87 ),
    inference(forward_demodulation,[],[f13728,f8824])).

fof(f13728,plain,
    ( ! [X336] :
        ( v1_relat_1(k1_relat_1(sK22(sK28(k1_tarski(X336)))))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X336)) )
    | ~ spl33_87 ),
    inference(superposition,[],[f8347,f3423])).

fof(f14133,plain,
    ( spl33_47
    | spl33_188
    | ~ spl33_75 ),
    inference(avatar_split_clause,[],[f13727,f6847,f14131,f3401])).

fof(f14131,plain,
    ( spl33_188
  <=> ! [X335] :
        ( k1_tarski(X335) = sK28(k1_tarski(X335))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X335)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_188])])).

fof(f13727,plain,
    ( ! [X335] :
        ( k1_tarski(X335) = sK28(k1_tarski(X335))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X335)) )
    | ~ spl33_75 ),
    inference(superposition,[],[f6849,f3423])).

fof(f6849,plain,
    ( k1_tarski(k1_xboole_0) = sK28(k1_tarski(k1_xboole_0))
    | ~ spl33_75 ),
    inference(avatar_component_clause,[],[f6847])).

fof(f14129,plain,
    ( spl33_47
    | spl33_187
    | spl33_73 ),
    inference(avatar_split_clause,[],[f13726,f6688,f14127,f3401])).

fof(f14127,plain,
    ( spl33_187
  <=> ! [X334] :
        ( ~ r2_hidden(k1_tarski(X334),sK28(k1_tarski(X334)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X334)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_187])])).

fof(f6688,plain,
    ( spl33_73
  <=> r2_hidden(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_73])])).

fof(f13726,plain,
    ( ! [X334] :
        ( ~ r2_hidden(k1_tarski(X334),sK28(k1_tarski(X334)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X334)) )
    | spl33_73 ),
    inference(superposition,[],[f6690,f3423])).

fof(f6690,plain,
    ( ~ r2_hidden(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0)))
    | spl33_73 ),
    inference(avatar_component_clause,[],[f6688])).

fof(f14125,plain,
    ( spl33_47
    | spl33_186
    | ~ spl33_72 ),
    inference(avatar_split_clause,[],[f13725,f6653,f14123,f3401])).

fof(f14123,plain,
    ( spl33_186
  <=> ! [X333] :
        ( r1_tarski(sK28(k1_tarski(X333)),k1_tarski(X333))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X333)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_186])])).

fof(f13725,plain,
    ( ! [X333] :
        ( r1_tarski(sK28(k1_tarski(X333)),k1_tarski(X333))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X333)) )
    | ~ spl33_72 ),
    inference(superposition,[],[f6655,f3423])).

fof(f14121,plain,
    ( spl33_47
    | spl33_185
    | ~ spl33_71 ),
    inference(avatar_split_clause,[],[f13724,f6411,f14119,f3401])).

fof(f14119,plain,
    ( spl33_185
  <=> ! [X332] :
        ( v1_relat_1(k1_tarski(k1_tarski(X332)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X332)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_185])])).

fof(f13724,plain,
    ( ! [X332] :
        ( v1_relat_1(k1_tarski(k1_tarski(X332)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X332)) )
    | ~ spl33_71 ),
    inference(superposition,[],[f6413,f3423])).

fof(f14117,plain,
    ( spl33_47
    | spl33_184
    | ~ spl33_66 ),
    inference(avatar_split_clause,[],[f13722,f5874,f14115,f3401])).

fof(f14115,plain,
    ( spl33_184
  <=> ! [X329] :
        ( v1_xboole_0(sK15(k1_tarski(X329)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X329)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_184])])).

fof(f5874,plain,
    ( spl33_66
  <=> v1_xboole_0(sK15(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_66])])).

fof(f13722,plain,
    ( ! [X329] :
        ( v1_xboole_0(sK15(k1_tarski(X329)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X329)) )
    | ~ spl33_66 ),
    inference(superposition,[],[f5876,f3423])).

fof(f5876,plain,
    ( v1_xboole_0(sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_66 ),
    inference(avatar_component_clause,[],[f5874])).

fof(f14113,plain,
    ( spl33_47
    | spl33_183
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f13721,f5757,f14111,f3401])).

fof(f14111,plain,
    ( spl33_183
  <=> ! [X328,X327] :
        ( ~ r2_hidden(X328,sK15(k1_tarski(X327)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X327)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_183])])).

fof(f13721,plain,
    ( ! [X327,X328] :
        ( ~ r2_hidden(X328,sK15(k1_tarski(X327)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X327)) )
    | ~ spl33_60 ),
    inference(superposition,[],[f5867,f3423])).

fof(f14109,plain,
    ( spl33_47
    | spl33_182
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f13719,f5757,f14107,f3401])).

fof(f14107,plain,
    ( spl33_182
  <=> ! [X324,X325] :
        ( r1_tarski(sK15(k1_tarski(X324)),X325)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X324)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_182])])).

fof(f13719,plain,
    ( ! [X325,X324] :
        ( r1_tarski(sK15(k1_tarski(X324)),X325)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X324)) )
    | ~ spl33_60 ),
    inference(superposition,[],[f5846,f3423])).

fof(f14105,plain,
    ( spl33_47
    | spl33_181
    | ~ spl33_63 ),
    inference(avatar_split_clause,[],[f13718,f5824,f14103,f3401])).

fof(f14103,plain,
    ( spl33_181
  <=> ! [X323] :
        ( v1_xboole_0(sK3(k1_tarski(X323)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X323)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_181])])).

fof(f5824,plain,
    ( spl33_63
  <=> v1_xboole_0(sK3(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_63])])).

fof(f13718,plain,
    ( ! [X323] :
        ( v1_xboole_0(sK3(k1_tarski(X323)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X323)) )
    | ~ spl33_63 ),
    inference(superposition,[],[f5826,f3423])).

fof(f5826,plain,
    ( v1_xboole_0(sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_63 ),
    inference(avatar_component_clause,[],[f5824])).

fof(f14101,plain,
    ( spl33_47
    | spl33_180
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f13717,f5752,f14099,f3401])).

fof(f14099,plain,
    ( spl33_180
  <=> ! [X322,X321] :
        ( ~ r2_hidden(X322,sK3(k1_tarski(X321)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X321)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_180])])).

fof(f13717,plain,
    ( ! [X321,X322] :
        ( ~ r2_hidden(X322,sK3(k1_tarski(X321)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X321)) )
    | ~ spl33_59 ),
    inference(superposition,[],[f5817,f3423])).

fof(f14097,plain,
    ( spl33_47
    | spl33_179
    | ~ spl33_61 ),
    inference(avatar_split_clause,[],[f13716,f5808,f14095,f3401])).

fof(f14095,plain,
    ( spl33_179
  <=> ! [X320] :
        ( k1_xboole_0 = sK3(k1_tarski(X320))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X320)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_179])])).

fof(f13716,plain,
    ( ! [X320] :
        ( k1_xboole_0 = sK3(k1_tarski(X320))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X320)) )
    | ~ spl33_61 ),
    inference(superposition,[],[f5810,f3423])).

fof(f14093,plain,
    ( spl33_47
    | spl33_178
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f13715,f5752,f14091,f3401])).

fof(f14091,plain,
    ( spl33_178
  <=> ! [X319,X318] :
        ( r1_tarski(sK3(k1_tarski(X318)),X319)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X318)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_178])])).

fof(f13715,plain,
    ( ! [X318,X319] :
        ( r1_tarski(sK3(k1_tarski(X318)),X319)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X318)) )
    | ~ spl33_59 ),
    inference(superposition,[],[f5796,f3423])).

fof(f14089,plain,
    ( spl33_47
    | spl33_177
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f13714,f5757,f14087,f3401])).

fof(f14087,plain,
    ( spl33_177
  <=> ! [X317] :
        ( r1_tarski(sK15(k1_tarski(X317)),k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X317)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_177])])).

fof(f13714,plain,
    ( ! [X317] :
        ( r1_tarski(sK15(k1_tarski(X317)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X317)) )
    | ~ spl33_60 ),
    inference(superposition,[],[f5759,f3423])).

fof(f14085,plain,
    ( spl33_47
    | spl33_176
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f13713,f5752,f14083,f3401])).

fof(f14083,plain,
    ( spl33_176
  <=> ! [X316] :
        ( r1_tarski(sK3(k1_tarski(X316)),k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X316)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_176])])).

fof(f13713,plain,
    ( ! [X316] :
        ( r1_tarski(sK3(k1_tarski(X316)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X316)) )
    | ~ spl33_59 ),
    inference(superposition,[],[f5754,f3423])).

fof(f14081,plain,
    ( spl33_47
    | spl33_175
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13712,f2259,f14079,f3401])).

fof(f14079,plain,
    ( spl33_175
  <=> ! [X314,X315,X313] :
        ( ~ m1_subset_1(X314,k1_tarski(X313))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X313))
        | ~ r1_tarski(X315,X314)
        | m1_subset_1(X315,k1_tarski(X313)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_175])])).

fof(f13712,plain,
    ( ! [X313,X315,X314] :
        ( ~ m1_subset_1(X314,k1_tarski(X313))
        | m1_subset_1(X315,k1_tarski(X313))
        | ~ r1_tarski(X315,X314)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X313)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f4707,f3423])).

fof(f4707,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_tarski(k1_xboole_0))
        | m1_subset_1(X2,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X2,X1) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f4706,f2261])).

fof(f4706,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X2,X1)
        | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f4699,f2261])).

fof(f4699,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X2,X1)
      | m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[],[f2104,f2228])).

fof(f14077,plain,
    ( spl33_47
    | spl33_174
    | spl33_51 ),
    inference(avatar_split_clause,[],[f13710,f3628,f14075,f3401])).

fof(f14075,plain,
    ( spl33_174
  <=> ! [X311] :
        ( ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(X311))),k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X311)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_174])])).

fof(f13710,plain,
    ( ! [X311] :
        ( ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(X311))),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X311)) )
    | spl33_51 ),
    inference(superposition,[],[f3630,f3423])).

fof(f14073,plain,
    ( spl33_47
    | spl33_173
    | spl33_49 ),
    inference(avatar_split_clause,[],[f13708,f3581,f14071,f3401])).

fof(f14071,plain,
    ( spl33_173
  <=> ! [X309] :
        ( ~ r1_tarski(k1_tarski(k1_tarski(k1_tarski(X309))),k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X309)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_173])])).

fof(f13708,plain,
    ( ! [X309] :
        ( ~ r1_tarski(k1_tarski(k1_tarski(k1_tarski(X309))),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X309)) )
    | spl33_49 ),
    inference(superposition,[],[f3583,f3423])).

fof(f14069,plain,
    ( spl33_47
    | spl33_172
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13707,f2259,f14067,f3401])).

fof(f14067,plain,
    ( spl33_172
  <=> ! [X307,X308] :
        ( m1_subset_1(k5_setfam_1(k1_xboole_0,X308),k1_tarski(X307))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X307))
        | ~ m1_subset_1(X308,k1_zfmisc_1(k1_tarski(X307))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_172])])).

fof(f13707,plain,
    ( ! [X308,X307] :
        ( m1_subset_1(k5_setfam_1(k1_xboole_0,X308),k1_tarski(X307))
        | ~ m1_subset_1(X308,k1_zfmisc_1(k1_tarski(X307)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X307)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f3571,f3423])).

fof(f14065,plain,
    ( spl33_47
    | spl33_171
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13706,f2259,f14063,f3401])).

fof(f14063,plain,
    ( spl33_171
  <=> ! [X305,X306,X304] :
        ( m1_subset_1(k9_subset_1(k1_xboole_0,X305,X306),k1_tarski(X304))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X304))
        | ~ m1_subset_1(X306,k1_tarski(X304)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_171])])).

fof(f13706,plain,
    ( ! [X304,X306,X305] :
        ( m1_subset_1(k9_subset_1(k1_xboole_0,X305,X306),k1_tarski(X304))
        | ~ m1_subset_1(X306,k1_tarski(X304))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X304)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f3549,f3423])).

fof(f14061,plain,
    ( spl33_47
    | spl33_170
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13705,f2259,f14059,f3401])).

fof(f14059,plain,
    ( spl33_170
  <=> ! [X303,X302] :
        ( ~ m1_subset_1(X303,k1_tarski(X302))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X302))
        | v1_relat_1(k1_relat_1(X303)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_170])])).

fof(f13705,plain,
    ( ! [X302,X303] :
        ( ~ m1_subset_1(X303,k1_tarski(X302))
        | v1_relat_1(k1_relat_1(X303))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X302)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f3505,f3423])).

fof(f14057,plain,
    ( spl33_47
    | spl33_169
    | ~ spl33_48 ),
    inference(avatar_split_clause,[],[f13704,f3405,f14055,f3401])).

fof(f14055,plain,
    ( spl33_169
  <=> ! [X301] :
        ( v1_relat_1(sK15(k1_tarski(X301)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X301)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_169])])).

fof(f3405,plain,
    ( spl33_48
  <=> v1_relat_1(sK15(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_48])])).

fof(f13704,plain,
    ( ! [X301] :
        ( v1_relat_1(sK15(k1_tarski(X301)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X301)) )
    | ~ spl33_48 ),
    inference(superposition,[],[f3407,f3423])).

fof(f3407,plain,
    ( v1_relat_1(sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_48 ),
    inference(avatar_component_clause,[],[f3405])).

fof(f14053,plain,
    ( spl33_47
    | spl33_168
    | ~ spl33_46 ),
    inference(avatar_split_clause,[],[f13703,f3396,f14051,f3401])).

fof(f14051,plain,
    ( spl33_168
  <=> ! [X300] :
        ( v1_relat_1(sK3(k1_tarski(X300)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X300)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_168])])).

fof(f3396,plain,
    ( spl33_46
  <=> v1_relat_1(sK3(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_46])])).

fof(f13703,plain,
    ( ! [X300] :
        ( v1_relat_1(sK3(k1_tarski(X300)))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X300)) )
    | ~ spl33_46 ),
    inference(superposition,[],[f3398,f3423])).

fof(f3398,plain,
    ( v1_relat_1(sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_46 ),
    inference(avatar_component_clause,[],[f3396])).

fof(f14049,plain,
    ( spl33_47
    | spl33_167
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(avatar_split_clause,[],[f13702,f2337,f2324,f2259,f14047,f3401])).

fof(f14047,plain,
    ( spl33_167
  <=> ! [X299,X298] :
        ( ~ m1_subset_1(X299,k1_tarski(X298))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X298))
        | v1_funct_1(X299) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_167])])).

fof(f13702,plain,
    ( ! [X298,X299] :
        ( ~ m1_subset_1(X299,k1_tarski(X298))
        | v1_funct_1(X299)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X298)) )
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(superposition,[],[f3158,f3423])).

fof(f3158,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_funct_1(X0) )
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(subsumption_resolution,[],[f3157,f2326])).

fof(f3157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_funct_1(X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl33_4
    | ~ spl33_18 ),
    inference(subsumption_resolution,[],[f3147,f2339])).

fof(f3147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_funct_1(X0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2109,f2261])).

fof(f14045,plain,
    ( spl33_47
    | spl33_166
    | ~ spl33_44 ),
    inference(avatar_split_clause,[],[f13701,f3152,f14043,f3401])).

fof(f14043,plain,
    ( spl33_166
  <=> ! [X297] :
        ( v1_funct_1(k1_tarski(X297))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X297)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_166])])).

fof(f13701,plain,
    ( ! [X297] :
        ( v1_funct_1(k1_tarski(X297))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X297)) )
    | ~ spl33_44 ),
    inference(superposition,[],[f3154,f3423])).

fof(f14041,plain,
    ( spl33_47
    | spl33_165 ),
    inference(avatar_split_clause,[],[f13700,f14039,f3401])).

fof(f14039,plain,
    ( spl33_165
  <=> ! [X295,X296,X294] :
        ( ~ r2_hidden(X295,k1_tarski(X294))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X294))
        | m1_subset_1(X295,k1_zfmisc_1(X296)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_165])])).

fof(f13700,plain,(
    ! [X294,X296,X295] :
      ( ~ r2_hidden(X295,k1_tarski(X294))
      | m1_subset_1(X295,k1_zfmisc_1(X296))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X294)) ) ),
    inference(superposition,[],[f3104,f3423])).

fof(f3104,plain,(
    ! [X17,X16] :
      ( ~ r2_hidden(X16,k1_tarski(k1_xboole_0))
      | m1_subset_1(X16,k1_zfmisc_1(X17)) ) ),
    inference(resolution,[],[f2007,f2077])).

fof(f14037,plain,
    ( spl33_47
    | spl33_164
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f13699,f2289,f2259,f14035,f3401])).

fof(f14035,plain,
    ( spl33_164
  <=> ! [X291,X293,X292] :
        ( ~ m1_subset_1(X292,k1_tarski(X291))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X291))
        | ~ r2_hidden(X293,X292) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_164])])).

fof(f13699,plain,
    ( ! [X292,X293,X291] :
        ( ~ m1_subset_1(X292,k1_tarski(X291))
        | ~ r2_hidden(X293,X292)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X291)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(superposition,[],[f2997,f3423])).

fof(f2997,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | ~ r2_hidden(X1,X0) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f2995,f2291])).

fof(f2995,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2125,f2261])).

fof(f14033,plain,
    ( spl33_47
    | spl33_163 ),
    inference(avatar_split_clause,[],[f13698,f14031,f3401])).

fof(f14031,plain,
    ( spl33_163
  <=> ! [X289,X290,X288] :
        ( ~ r2_hidden(X289,k1_tarski(X288))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X288))
        | r2_hidden(X289,k1_zfmisc_1(X290)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_163])])).

fof(f13698,plain,(
    ! [X288,X290,X289] :
      ( ~ r2_hidden(X289,k1_tarski(X288))
      | r2_hidden(X289,k1_zfmisc_1(X290))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X288)) ) ),
    inference(superposition,[],[f2869,f3423])).

fof(f2869,plain,(
    ! [X35,X34] :
      ( ~ r2_hidden(X34,k1_tarski(k1_xboole_0))
      | r2_hidden(X34,k1_zfmisc_1(X35)) ) ),
    inference(resolution,[],[f2015,f2465])).

fof(f14029,plain,
    ( spl33_47
    | spl33_162
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f13697,f2289,f2259,f14027,f3401])).

fof(f14027,plain,
    ( spl33_162
  <=> ! [X286,X287] :
        ( ~ m1_subset_1(X287,k1_tarski(X286))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X286))
        | v1_xboole_0(X287) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_162])])).

fof(f13697,plain,
    ( ! [X287,X286] :
        ( ~ m1_subset_1(X287,k1_tarski(X286))
        | v1_xboole_0(X287)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X286)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(superposition,[],[f2795,f3423])).

fof(f14025,plain,
    ( spl33_47
    | spl33_161 ),
    inference(avatar_split_clause,[],[f13696,f14023,f3401])).

fof(f14023,plain,
    ( spl33_161
  <=> ! [X284,X285] :
        ( r2_hidden(k1_tarski(X284),k1_zfmisc_1(k1_zfmisc_1(X285)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X284)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_161])])).

fof(f13696,plain,(
    ! [X285,X284] :
      ( r2_hidden(k1_tarski(X284),k1_zfmisc_1(k1_zfmisc_1(X285)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X284)) ) ),
    inference(superposition,[],[f2767,f3423])).

fof(f14021,plain,
    ( spl33_47
    | spl33_160
    | spl33_34 ),
    inference(avatar_split_clause,[],[f13694,f2732,f14019,f3401])).

fof(f14019,plain,
    ( spl33_160
  <=> ! [X281] :
        ( ~ v1_relat_1(k1_tarski(X281))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X281)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_160])])).

fof(f13694,plain,
    ( ! [X281] :
        ( ~ v1_relat_1(k1_tarski(X281))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X281)) )
    | spl33_34 ),
    inference(superposition,[],[f2733,f3423])).

fof(f14017,plain,
    ( spl33_47
    | spl33_159
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13693,f2259,f14015,f3401])).

fof(f14015,plain,
    ( spl33_159
  <=> ! [X279,X280] :
        ( ~ m1_subset_1(X280,k1_tarski(X279))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X279))
        | v1_relat_1(X280) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_159])])).

fof(f13693,plain,
    ( ! [X280,X279] :
        ( ~ m1_subset_1(X280,k1_tarski(X279))
        | v1_relat_1(X280)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X279)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2702,f3423])).

fof(f2702,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_tarski(k1_xboole_0))
        | v1_relat_1(X1) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f2699,f2261])).

fof(f2699,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_relat_1(X1) ) ),
    inference(superposition,[],[f2105,f2228])).

fof(f14013,plain,
    ( spl33_47
    | spl33_158
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13690,f2259,f14011,f3401])).

fof(f14011,plain,
    ( spl33_158
  <=> ! [X274,X275] :
        ( ~ r2_hidden(X275,k1_tarski(X274))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X274))
        | r1_tarski(X275,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_158])])).

fof(f13690,plain,
    ( ! [X275,X274] :
        ( ~ r2_hidden(X275,k1_tarski(X274))
        | r1_tarski(X275,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X274)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2600,f3423])).

fof(f14009,plain,
    ( spl33_47
    | spl33_157
    | spl33_31 ),
    inference(avatar_split_clause,[],[f13689,f2590,f14007,f3401])).

fof(f14007,plain,
    ( spl33_157
  <=> ! [X273] :
        ( ~ r1_tarski(k1_tarski(k1_tarski(X273)),k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X273)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_157])])).

fof(f13689,plain,
    ( ! [X273] :
        ( ~ r1_tarski(k1_tarski(k1_tarski(X273)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X273)) )
    | spl33_31 ),
    inference(superposition,[],[f2592,f3423])).

fof(f14005,plain,
    ( spl33_47
    | spl33_156
    | ~ spl33_29 ),
    inference(avatar_split_clause,[],[f14004,f2507,f14000,f3401])).

fof(f14004,plain,
    ( ! [X269] :
        ( r1_tarski(X269,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X269)) )
    | ~ spl33_29 ),
    inference(forward_demodulation,[],[f13686,f2612])).

fof(f2612,plain,(
    ! [X4] : sK27(k1_tarski(X4)) = X4 ),
    inference(subsumption_resolution,[],[f2611,f2161])).

fof(f2611,plain,(
    ! [X4] :
      ( sK27(k1_tarski(X4)) = X4
      | v1_xboole_0(k1_tarski(X4)) ) ),
    inference(resolution,[],[f2238,f2146])).

fof(f13686,plain,
    ( ! [X269] :
        ( r1_tarski(sK27(k1_tarski(X269)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X269)) )
    | ~ spl33_29 ),
    inference(superposition,[],[f2509,f3423])).

fof(f14002,plain,
    ( spl33_47
    | spl33_156
    | ~ spl33_27 ),
    inference(avatar_split_clause,[],[f13998,f2493,f14000,f3401])).

fof(f13998,plain,
    ( ! [X267] :
        ( r1_tarski(X267,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X267)) )
    | ~ spl33_27 ),
    inference(forward_demodulation,[],[f13684,f2803])).

fof(f2803,plain,(
    ! [X3] : sK22(k1_tarski(X3)) = X3 ),
    inference(subsumption_resolution,[],[f2800,f2161])).

fof(f2800,plain,(
    ! [X3] :
      ( v1_xboole_0(k1_tarski(X3))
      | sK22(k1_tarski(X3)) = X3 ) ),
    inference(resolution,[],[f2761,f2238])).

fof(f13684,plain,
    ( ! [X267] :
        ( r1_tarski(sK22(k1_tarski(X267)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X267)) )
    | ~ spl33_27 ),
    inference(superposition,[],[f2495,f3423])).

fof(f13996,plain,
    ( spl33_47
    | spl33_155 ),
    inference(avatar_split_clause,[],[f13682,f13994,f3401])).

fof(f13994,plain,
    ( spl33_155
  <=> ! [X264,X265] :
        ( ~ r2_hidden(k1_zfmisc_1(X265),k1_tarski(X264))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X264)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_155])])).

fof(f13682,plain,(
    ! [X265,X264] :
      ( ~ r2_hidden(k1_zfmisc_1(X265),k1_tarski(X264))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X264)) ) ),
    inference(superposition,[],[f2480,f3423])).

fof(f13992,plain,
    ( spl33_47
    | spl33_154
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f13680,f2259,f13990,f3401])).

fof(f13990,plain,
    ( spl33_154
  <=> ! [X260,X261] :
        ( ~ m1_subset_1(X261,k1_tarski(X260))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X260))
        | r1_tarski(X261,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_154])])).

fof(f13680,plain,
    ( ! [X261,X260] :
        ( ~ m1_subset_1(X261,k1_tarski(X260))
        | r1_tarski(X261,k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X260)) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2469,f3423])).

fof(f2469,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(superposition,[],[f2106,f2261])).

fof(f13988,plain,
    ( spl33_47
    | spl33_153 ),
    inference(avatar_split_clause,[],[f13679,f13986,f3401])).

fof(f13986,plain,
    ( spl33_153
  <=> ! [X258,X259] :
        ( r1_tarski(k1_tarski(X258),k1_zfmisc_1(X259))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X258)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_153])])).

fof(f13679,plain,(
    ! [X259,X258] :
      ( r1_tarski(k1_tarski(X258),k1_zfmisc_1(X259))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X258)) ) ),
    inference(superposition,[],[f2465,f3423])).

fof(f13983,plain,
    ( spl33_47
    | spl33_152 ),
    inference(avatar_split_clause,[],[f13675,f13981,f3401])).

fof(f13981,plain,
    ( spl33_152
  <=> ! [X252,X253] :
        ( m1_subset_1(k1_tarski(X252),k1_zfmisc_1(k1_zfmisc_1(X253)))
        | ~ r2_hidden(k1_xboole_0,k1_tarski(X252)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_152])])).

fof(f13675,plain,(
    ! [X253,X252] :
      ( m1_subset_1(k1_tarski(X252),k1_zfmisc_1(k1_zfmisc_1(X253)))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ r2_hidden(k1_xboole_0,k1_tarski(X252)) ) ),
    inference(superposition,[],[f2077,f3423])).

fof(f12962,plain,
    ( spl33_47
    | spl33_151
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12940,f2259,f12960,f3401])).

fof(f12960,plain,
    ( spl33_151
  <=> ! [X34,X35] :
        ( m1_subset_1(X34,k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X35))
        | ~ r1_tarski(X34,sK14(X35,k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_151])])).

fof(f12940,plain,
    ( ! [X35,X34] :
        ( m1_subset_1(X34,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X34,sK14(X35,k1_tarski(k1_xboole_0)))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X35))
        | k1_xboole_0 = k1_tarski(k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f4707,f3776])).

fof(f3776,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK14(X10,X9),X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(X10))
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f2061,f2034])).

fof(f12958,plain,
    ( spl33_47
    | spl33_150
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12938,f2259,f12956,f3401])).

fof(f12956,plain,
    ( spl33_150
  <=> ! [X31,X30] :
        ( m1_subset_1(X30,k1_tarski(k1_xboole_0))
        | k1_tarski(k1_xboole_0) = k1_tarski(X31)
        | ~ r1_tarski(X30,sK13(k1_tarski(k1_xboole_0),X31)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_150])])).

fof(f12938,plain,
    ( ! [X30,X31] :
        ( m1_subset_1(X30,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X30,sK13(k1_tarski(k1_xboole_0),X31))
        | k1_tarski(k1_xboole_0) = k1_tarski(X31)
        | k1_xboole_0 = k1_tarski(k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f4707,f3677])).

fof(f3677,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK13(X9,X10),X9)
      | k1_tarski(X10) = X9
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f2046,f2034])).

fof(f12954,plain,
    ( spl33_47
    | spl33_149
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12937,f2259,f12952,f3401])).

fof(f12952,plain,
    ( spl33_149
  <=> ! [X29,X28] :
        ( m1_subset_1(X28,k1_tarski(k1_xboole_0))
        | k1_tarski(k1_xboole_0) = k1_tarski(X29)
        | ~ r1_tarski(X28,sK12(k1_tarski(k1_xboole_0),X29)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_149])])).

fof(f12937,plain,
    ( ! [X28,X29] :
        ( m1_subset_1(X28,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X28,sK12(k1_tarski(k1_xboole_0),X29))
        | k1_tarski(k1_xboole_0) = k1_tarski(X29)
        | k1_xboole_0 = k1_tarski(k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f4707,f3648])).

fof(f3648,plain,(
    ! [X10,X9] :
      ( m1_subset_1(sK12(X9,X10),X9)
      | k1_tarski(X10) = X9
      | k1_xboole_0 = X9 ) ),
    inference(resolution,[],[f2044,f2034])).

fof(f12721,plain,
    ( spl33_47
    | spl33_148
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12676,f2259,f12719,f3401])).

fof(f12719,plain,
    ( spl33_148
  <=> ! [X12] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X12))
        | v1_relat_1(sK14(X12,k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_148])])).

fof(f12676,plain,
    ( ! [X12] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X12))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(sK14(X12,k1_tarski(k1_xboole_0))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3776,f2702])).

fof(f12717,plain,
    ( spl33_47
    | spl33_147
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12674,f2289,f2259,f12715,f3401])).

fof(f12715,plain,
    ( spl33_147
  <=> ! [X10] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X10))
        | v1_xboole_0(sK14(X10,k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_147])])).

fof(f12674,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X10))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_xboole_0(sK14(X10,k1_tarski(k1_xboole_0))) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3776,f2795])).

fof(f12713,plain,
    ( spl33_47
    | spl33_146
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12673,f2259,f12711,f3401])).

fof(f12711,plain,
    ( spl33_146
  <=> ! [X9] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X9))
        | v1_relat_1(k1_relat_1(sK14(X9,k1_tarski(k1_xboole_0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_146])])).

fof(f12673,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X9))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_relat_1(sK14(X9,k1_tarski(k1_xboole_0)))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3776,f3505])).

fof(f12709,plain,
    ( spl33_47
    | spl33_145
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12672,f2289,f2259,f12707,f3401])).

fof(f12707,plain,
    ( spl33_145
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X7))
        | ~ r2_hidden(X8,sK14(X7,k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_145])])).

fof(f12672,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X7))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(X8,sK14(X7,k1_tarski(k1_xboole_0))) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3776,f2997])).

fof(f12705,plain,
    ( spl33_47
    | spl33_144
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(avatar_split_clause,[],[f12671,f2337,f2324,f2259,f12703,f3401])).

fof(f12703,plain,
    ( spl33_144
  <=> ! [X6] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X6))
        | v1_funct_1(sK14(X6,k1_tarski(k1_xboole_0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_144])])).

fof(f12671,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X6))
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(sK14(X6,k1_tarski(k1_xboole_0))) )
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(resolution,[],[f3776,f3158])).

fof(f12629,plain,
    ( spl33_110
    | spl33_143 ),
    inference(avatar_split_clause,[],[f12597,f12627,f9799])).

fof(f12627,plain,
    ( spl33_143
  <=> ! [X22] :
        ( ~ v1_xboole_0(X22)
        | v1_funct_1(k5_setfam_1(k1_xboole_0,X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_143])])).

fof(f12597,plain,(
    ! [X23,X22] :
      ( ~ v1_xboole_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X23)
      | v1_funct_1(k5_setfam_1(k1_xboole_0,X22)) ) ),
    inference(resolution,[],[f11807,f3134])).

fof(f11807,plain,(
    ! [X30,X29] :
      ( r1_tarski(k5_setfam_1(k1_xboole_0,X29),X30)
      | ~ v1_xboole_0(X29) ) ),
    inference(resolution,[],[f9661,f2896])).

fof(f9661,plain,(
    ! [X2,X3] :
      ( r1_tarski(k5_setfam_1(X2,X3),X2)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f3560,f2347])).

fof(f12571,plain,
    ( spl33_47
    | spl33_142
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12526,f2259,f12569,f3401])).

fof(f12569,plain,
    ( spl33_142
  <=> ! [X12] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X12)
        | v1_relat_1(sK13(k1_tarski(k1_xboole_0),X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_142])])).

fof(f12526,plain,
    ( ! [X12] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X12)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(sK13(k1_tarski(k1_xboole_0),X12)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3677,f2702])).

fof(f12567,plain,
    ( spl33_47
    | spl33_141
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12524,f2289,f2259,f12565,f3401])).

fof(f12565,plain,
    ( spl33_141
  <=> ! [X10] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X10)
        | v1_xboole_0(sK13(k1_tarski(k1_xboole_0),X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_141])])).

fof(f12524,plain,
    ( ! [X10] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X10)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_xboole_0(sK13(k1_tarski(k1_xboole_0),X10)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3677,f2795])).

fof(f12563,plain,
    ( spl33_47
    | spl33_140
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12523,f2259,f12561,f3401])).

fof(f12561,plain,
    ( spl33_140
  <=> ! [X9] :
        ( k1_tarski(X9) = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_relat_1(sK13(k1_tarski(k1_xboole_0),X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_140])])).

fof(f12523,plain,
    ( ! [X9] :
        ( k1_tarski(X9) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_relat_1(sK13(k1_tarski(k1_xboole_0),X9))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3677,f3505])).

fof(f12559,plain,
    ( spl33_47
    | spl33_139
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12522,f2289,f2259,f12557,f3401])).

fof(f12557,plain,
    ( spl33_139
  <=> ! [X7,X8] :
        ( k1_tarski(X7) = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(X8,sK13(k1_tarski(k1_xboole_0),X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_139])])).

fof(f12522,plain,
    ( ! [X8,X7] :
        ( k1_tarski(X7) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(X8,sK13(k1_tarski(k1_xboole_0),X7)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3677,f2997])).

fof(f12555,plain,
    ( spl33_47
    | spl33_138
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(avatar_split_clause,[],[f12521,f2337,f2324,f2259,f12553,f3401])).

fof(f12553,plain,
    ( spl33_138
  <=> ! [X6] :
        ( k1_tarski(X6) = k1_tarski(k1_xboole_0)
        | v1_funct_1(sK13(k1_tarski(k1_xboole_0),X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_138])])).

fof(f12521,plain,
    ( ! [X6] :
        ( k1_tarski(X6) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(sK13(k1_tarski(k1_xboole_0),X6)) )
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(resolution,[],[f3677,f3158])).

fof(f12450,plain,
    ( spl33_47
    | spl33_137
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12405,f2259,f12448,f3401])).

fof(f12448,plain,
    ( spl33_137
  <=> ! [X12] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X12)
        | v1_relat_1(sK12(k1_tarski(k1_xboole_0),X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_137])])).

fof(f12405,plain,
    ( ! [X12] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X12)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(sK12(k1_tarski(k1_xboole_0),X12)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3648,f2702])).

fof(f12446,plain,
    ( spl33_47
    | spl33_136
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12403,f2289,f2259,f12444,f3401])).

fof(f12444,plain,
    ( spl33_136
  <=> ! [X10] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X10)
        | v1_xboole_0(sK12(k1_tarski(k1_xboole_0),X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_136])])).

fof(f12403,plain,
    ( ! [X10] :
        ( k1_tarski(k1_xboole_0) = k1_tarski(X10)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_xboole_0(sK12(k1_tarski(k1_xboole_0),X10)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3648,f2795])).

fof(f12442,plain,
    ( spl33_47
    | spl33_135
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f12402,f2259,f12440,f3401])).

fof(f12440,plain,
    ( spl33_135
  <=> ! [X9] :
        ( k1_tarski(X9) = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_relat_1(sK12(k1_tarski(k1_xboole_0),X9))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_135])])).

fof(f12402,plain,
    ( ! [X9] :
        ( k1_tarski(X9) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_relat_1(k1_relat_1(sK12(k1_tarski(k1_xboole_0),X9))) )
    | ~ spl33_4 ),
    inference(resolution,[],[f3648,f3505])).

fof(f12438,plain,
    ( spl33_47
    | spl33_134
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f12401,f2289,f2259,f12436,f3401])).

fof(f12436,plain,
    ( spl33_134
  <=> ! [X7,X8] :
        ( k1_tarski(X7) = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(X8,sK12(k1_tarski(k1_xboole_0),X7)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_134])])).

fof(f12401,plain,
    ( ! [X8,X7] :
        ( k1_tarski(X7) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ r2_hidden(X8,sK12(k1_tarski(k1_xboole_0),X7)) )
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f3648,f2997])).

fof(f12434,plain,
    ( spl33_47
    | spl33_133
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(avatar_split_clause,[],[f12400,f2337,f2324,f2259,f12432,f3401])).

fof(f12432,plain,
    ( spl33_133
  <=> ! [X6] :
        ( k1_tarski(X6) = k1_tarski(k1_xboole_0)
        | v1_funct_1(sK12(k1_tarski(k1_xboole_0),X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_133])])).

fof(f12400,plain,
    ( ! [X6] :
        ( k1_tarski(X6) = k1_tarski(k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | v1_funct_1(sK12(k1_tarski(k1_xboole_0),X6)) )
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(resolution,[],[f3648,f3158])).

fof(f11957,plain,
    ( spl33_132
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11952,f2259,f11954])).

fof(f11954,plain,
    ( spl33_132
  <=> k1_xboole_0 = k3_tarski(sK26(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_132])])).

fof(f11952,plain,
    ( k1_xboole_0 = k3_tarski(sK26(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11916,f2261])).

fof(f11916,plain,(
    k1_xboole_0 = k3_tarski(sK26(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f11889,f2075])).

fof(f11950,plain,
    ( spl33_131
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11945,f2259,f11947])).

fof(f11947,plain,
    ( spl33_131
  <=> v1_relat_1(k3_tarski(sK26(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_131])])).

fof(f11945,plain,
    ( v1_relat_1(k3_tarski(sK26(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11914,f2261])).

fof(f11914,plain,(
    v1_relat_1(k3_tarski(sK26(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(resolution,[],[f11889,f3351])).

fof(f11944,plain,
    ( spl33_130
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f11939,f2289,f2259,f11941])).

fof(f11941,plain,
    ( spl33_130
  <=> v1_xboole_0(k3_tarski(sK26(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_130])])).

fof(f11939,plain,
    ( v1_xboole_0(k3_tarski(sK26(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(forward_demodulation,[],[f11913,f2261])).

fof(f11913,plain,
    ( v1_xboole_0(k3_tarski(sK26(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f11889,f6277])).

fof(f11938,plain,
    ( spl33_129
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11933,f2259,f11935])).

fof(f11935,plain,
    ( spl33_129
  <=> v1_relat_1(k1_relat_1(k3_tarski(sK26(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_129])])).

fof(f11933,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(sK26(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11912,f2261])).

fof(f11912,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(sK26(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f11889,f7349])).

fof(f11888,plain,
    ( spl33_128
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11883,f2259,f11885])).

fof(f11885,plain,
    ( spl33_128
  <=> k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_128])])).

fof(f11883,plain,
    ( k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11847,f2261])).

fof(f11847,plain,(
    k1_xboole_0 = k5_setfam_1(k1_xboole_0,sK26(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f9687,f2075])).

fof(f11881,plain,
    ( spl33_127
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11876,f2259,f11878])).

fof(f11878,plain,
    ( spl33_127
  <=> v1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_127])])).

fof(f11876,plain,
    ( v1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11845,f2261])).

fof(f11845,plain,(
    v1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_zfmisc_1(k1_xboole_0)))) ),
    inference(resolution,[],[f9687,f3351])).

fof(f11875,plain,
    ( spl33_126
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f11870,f2289,f2259,f11872])).

fof(f11872,plain,
    ( spl33_126
  <=> v1_xboole_0(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_126])])).

fof(f11870,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(forward_demodulation,[],[f11844,f2261])).

fof(f11844,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,sK26(k1_zfmisc_1(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f9687,f6277])).

fof(f11869,plain,
    ( spl33_125
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f11864,f2259,f11866])).

fof(f11866,plain,
    ( spl33_125
  <=> v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_125])])).

fof(f11864,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f11843,f2261])).

fof(f11843,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,sK26(k1_zfmisc_1(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f9687,f7349])).

fof(f11286,plain,
    ( ~ spl33_11
    | ~ spl33_12
    | ~ spl33_110 ),
    inference(avatar_contradiction_clause,[],[f11285])).

fof(f11285,plain,
    ( $false
    | ~ spl33_11
    | ~ spl33_12
    | ~ spl33_110 ),
    inference(subsumption_resolution,[],[f11260,f2301])).

fof(f2301,plain,
    ( v1_relat_1(sK31)
    | ~ spl33_12 ),
    inference(avatar_component_clause,[],[f2299])).

fof(f2299,plain,
    ( spl33_12
  <=> v1_relat_1(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_12])])).

fof(f11260,plain,
    ( ~ v1_relat_1(sK31)
    | ~ spl33_11
    | ~ spl33_110 ),
    inference(resolution,[],[f9800,f2296])).

fof(f2296,plain,
    ( v1_funct_1(sK31)
    | ~ spl33_11 ),
    inference(avatar_component_clause,[],[f2294])).

fof(f2294,plain,
    ( spl33_11
  <=> v1_funct_1(sK31) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_11])])).

fof(f9800,plain,
    ( ! [X13] :
        ( ~ v1_funct_1(X13)
        | ~ v1_relat_1(X13) )
    | ~ spl33_110 ),
    inference(avatar_component_clause,[],[f9799])).

fof(f11283,plain,
    ( ~ spl33_92
    | ~ spl33_96
    | ~ spl33_110 ),
    inference(avatar_contradiction_clause,[],[f11282])).

fof(f11282,plain,
    ( $false
    | ~ spl33_92
    | ~ spl33_96
    | ~ spl33_110 ),
    inference(subsumption_resolution,[],[f11257,f8583])).

fof(f11257,plain,
    ( ~ v1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_92
    | ~ spl33_110 ),
    inference(resolution,[],[f9800,f8558])).

fof(f11279,plain,(
    ~ spl33_110 ),
    inference(avatar_contradiction_clause,[],[f11278])).

fof(f11278,plain,
    ( $false
    | ~ spl33_110 ),
    inference(subsumption_resolution,[],[f11254,f2315])).

fof(f2315,plain,(
    ! [X0] : v1_relat_1(sK26(X0)) ),
    inference(resolution,[],[f2154,f2144])).

fof(f2144,plain,(
    ! [X0] : v1_xboole_0(sK26(X0)) ),
    inference(cnf_transformation,[],[f1979])).

fof(f2154,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1861])).

fof(f1861,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f638])).

fof(f638,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f11254,plain,
    ( ! [X23] : ~ v1_relat_1(sK26(X23))
    | ~ spl33_110 ),
    inference(resolution,[],[f9800,f2328])).

fof(f2328,plain,(
    ! [X0] : v1_funct_1(sK26(X0)) ),
    inference(resolution,[],[f2155,f2144])).

fof(f2155,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f1862])).

fof(f1862,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f890])).

fof(f890,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_1)).

fof(f11277,plain,
    ( ~ spl33_15
    | ~ spl33_17
    | ~ spl33_110 ),
    inference(avatar_contradiction_clause,[],[f11276])).

fof(f11276,plain,
    ( $false
    | ~ spl33_15
    | ~ spl33_17
    | ~ spl33_110 ),
    inference(subsumption_resolution,[],[f11253,f2321])).

fof(f2321,plain,
    ( v1_relat_1(sK24)
    | ~ spl33_15 ),
    inference(avatar_component_clause,[],[f2319])).

fof(f2319,plain,
    ( spl33_15
  <=> v1_relat_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_15])])).

fof(f11253,plain,
    ( ~ v1_relat_1(sK24)
    | ~ spl33_17
    | ~ spl33_110 ),
    inference(resolution,[],[f9800,f2334])).

fof(f2334,plain,
    ( v1_funct_1(sK24)
    | ~ spl33_17 ),
    inference(avatar_component_clause,[],[f2332])).

fof(f2332,plain,
    ( spl33_17
  <=> v1_funct_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_17])])).

fof(f11262,plain,
    ( ~ spl33_16
    | ~ spl33_18
    | ~ spl33_110 ),
    inference(avatar_contradiction_clause,[],[f11261])).

fof(f11261,plain,
    ( $false
    | ~ spl33_16
    | ~ spl33_18
    | ~ spl33_110 ),
    inference(subsumption_resolution,[],[f11236,f2326])).

fof(f11236,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ spl33_18
    | ~ spl33_110 ),
    inference(resolution,[],[f9800,f2339])).

fof(f11217,plain,
    ( spl33_56
    | spl33_122 ),
    inference(avatar_split_clause,[],[f11182,f11206,f4925])).

fof(f11206,plain,
    ( spl33_122
  <=> ! [X12] :
        ( ~ v1_xboole_0(X12)
        | v1_relat_1(k3_tarski(X12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_122])])).

fof(f11182,plain,(
    ! [X24,X25] :
      ( ~ v1_xboole_0(X24)
      | v1_relat_1(k3_tarski(X24))
      | ~ v1_xboole_0(X25) ) ),
    inference(resolution,[],[f9780,f3352])).

fof(f9780,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f9746,f2152])).

fof(f11216,plain,
    ( spl33_110
    | spl33_124 ),
    inference(avatar_split_clause,[],[f11181,f11214,f9799])).

fof(f11214,plain,
    ( spl33_124
  <=> ! [X22] :
        ( ~ v1_xboole_0(X22)
        | v1_funct_1(k3_tarski(X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_124])])).

fof(f11181,plain,(
    ! [X23,X22] :
      ( ~ v1_xboole_0(X22)
      | ~ v1_funct_1(X23)
      | ~ v1_relat_1(X23)
      | v1_funct_1(k3_tarski(X22)) ) ),
    inference(resolution,[],[f9780,f3134])).

fof(f11212,plain,
    ( spl33_56
    | spl33_123 ),
    inference(avatar_split_clause,[],[f11178,f11210,f4925])).

fof(f11210,plain,
    ( spl33_123
  <=> ! [X14] :
        ( ~ v1_xboole_0(X14)
        | v1_xboole_0(k3_tarski(X14)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_123])])).

fof(f11178,plain,(
    ! [X14,X15] :
      ( ~ v1_xboole_0(X14)
      | ~ v1_xboole_0(X15)
      | v1_xboole_0(k3_tarski(X14)) ) ),
    inference(resolution,[],[f9780,f2782])).

fof(f11208,plain,
    ( spl33_107
    | spl33_122 ),
    inference(avatar_split_clause,[],[f11177,f11206,f9786])).

fof(f11177,plain,(
    ! [X12,X13] :
      ( ~ v1_xboole_0(X12)
      | ~ v1_relat_1(X13)
      | v1_relat_1(k3_tarski(X12)) ) ),
    inference(resolution,[],[f9780,f2716])).

fof(f10111,plain,(
    spl33_120 ),
    inference(avatar_split_clause,[],[f10072,f10093])).

fof(f10093,plain,
    ( spl33_120
  <=> v1_relat_1(k1_relat_1(k3_tarski(k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_120])])).

fof(f10072,plain,(
    v1_relat_1(k1_relat_1(k3_tarski(k1_tarski(k1_xboole_0)))) ),
    inference(resolution,[],[f10041,f3480])).

fof(f3480,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
      | v1_relat_1(k1_relat_1(X0)) ) ),
    inference(resolution,[],[f2201,f2107])).

fof(f10110,plain,(
    spl33_117 ),
    inference(avatar_split_clause,[],[f10071,f10077])).

fof(f10077,plain,
    ( spl33_117
  <=> v1_relat_1(k3_tarski(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_117])])).

fof(f10071,plain,(
    v1_relat_1(k3_tarski(k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f10041,f2689])).

fof(f10109,plain,
    ( spl33_118
    | spl33_56 ),
    inference(avatar_split_clause,[],[f10070,f4925,f10082])).

fof(f10082,plain,
    ( spl33_118
  <=> v1_xboole_0(k3_tarski(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_118])])).

fof(f10070,plain,(
    ! [X23] :
      ( ~ v1_xboole_0(X23)
      | v1_xboole_0(k3_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f10041,f3253])).

fof(f3253,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2133,f2107])).

fof(f10108,plain,
    ( spl33_118
    | spl33_56 ),
    inference(avatar_split_clause,[],[f10069,f4925,f10082])).

fof(f10069,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | v1_xboole_0(k3_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f10041,f3283])).

fof(f3283,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X2,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f2134,f2107])).

fof(f10107,plain,(
    spl33_121 ),
    inference(avatar_split_clause,[],[f10068,f10100])).

fof(f10068,plain,(
    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f10041,f2058])).

fof(f10106,plain,(
    spl33_121 ),
    inference(avatar_split_clause,[],[f10066,f10100])).

fof(f10066,plain,(
    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f10041,f2057])).

fof(f10105,plain,(
    spl33_121 ),
    inference(avatar_split_clause,[],[f10104,f10100])).

fof(f10104,plain,(
    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    inference(global_subsumption,[],[f10061])).

fof(f10061,plain,(
    k1_xboole_0 = k3_tarski(k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f10041,f2075])).

fof(f10103,plain,(
    spl33_121 ),
    inference(avatar_split_clause,[],[f10061,f10100])).

fof(f10098,plain,(
    spl33_117 ),
    inference(avatar_split_clause,[],[f10059,f10077])).

fof(f10059,plain,(
    v1_relat_1(k3_tarski(k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f10041,f3351])).

fof(f10097,plain,
    ( spl33_118
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f10058,f2289,f2259,f10082])).

fof(f10058,plain,
    ( v1_xboole_0(k3_tarski(k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f10041,f6277])).

fof(f10096,plain,
    ( spl33_120
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f10057,f2259,f10093])).

fof(f10057,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(resolution,[],[f10041,f7349])).

fof(f10091,plain,
    ( spl33_56
    | spl33_117 ),
    inference(avatar_split_clause,[],[f10056,f10077,f4925])).

fof(f10056,plain,(
    ! [X14] :
      ( v1_relat_1(k3_tarski(k1_tarski(k1_xboole_0)))
      | ~ v1_xboole_0(X14) ) ),
    inference(resolution,[],[f10041,f3352])).

fof(f10090,plain,
    ( spl33_119
    | spl33_110 ),
    inference(avatar_split_clause,[],[f10055,f9799,f10087])).

fof(f10087,plain,
    ( spl33_119
  <=> v1_funct_1(k3_tarski(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_119])])).

fof(f10055,plain,(
    ! [X13] :
      ( ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | v1_funct_1(k3_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f10041,f3134])).

fof(f10085,plain,
    ( spl33_118
    | spl33_56 ),
    inference(avatar_split_clause,[],[f10052,f4925,f10082])).

fof(f10052,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | v1_xboole_0(k3_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f10041,f2782])).

fof(f10080,plain,
    ( spl33_117
    | spl33_107 ),
    inference(avatar_split_clause,[],[f10051,f9786,f10077])).

fof(f10051,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | v1_relat_1(k3_tarski(k1_tarski(k1_xboole_0))) ) ),
    inference(resolution,[],[f10041,f2716])).

fof(f10040,plain,(
    spl33_116 ),
    inference(avatar_split_clause,[],[f10009,f10037])).

fof(f10009,plain,(
    k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f9665,f2075])).

fof(f10035,plain,(
    spl33_115 ),
    inference(avatar_split_clause,[],[f10007,f10032])).

fof(f10032,plain,
    ( spl33_115
  <=> v1_relat_1(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_115])])).

fof(f10007,plain,(
    v1_relat_1(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f9665,f3351])).

fof(f10030,plain,
    ( spl33_114
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f10006,f2289,f2259,f10027])).

fof(f10027,plain,
    ( spl33_114
  <=> v1_xboole_0(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_114])])).

fof(f10006,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0)))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f9665,f6277])).

fof(f10025,plain,
    ( spl33_113
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f10005,f2259,f10022])).

fof(f10022,plain,
    ( spl33_113
  <=> v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_113])])).

fof(f10005,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(resolution,[],[f9665,f7349])).

fof(f9822,plain,(
    spl33_111 ),
    inference(avatar_split_clause,[],[f9777,f9804])).

fof(f9804,plain,
    ( spl33_111
  <=> v1_relat_1(k1_relat_1(k3_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_111])])).

fof(f9777,plain,(
    v1_relat_1(k1_relat_1(k3_tarski(k1_xboole_0))) ),
    inference(resolution,[],[f9746,f3480])).

fof(f9821,plain,(
    spl33_106 ),
    inference(avatar_split_clause,[],[f9776,f9782])).

fof(f9782,plain,
    ( spl33_106
  <=> v1_relat_1(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_106])])).

fof(f9776,plain,(
    v1_relat_1(k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f9746,f2689])).

fof(f9820,plain,
    ( spl33_108
    | spl33_56 ),
    inference(avatar_split_clause,[],[f9775,f4925,f9790])).

fof(f9790,plain,
    ( spl33_108
  <=> v1_xboole_0(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_108])])).

fof(f9775,plain,(
    ! [X23] :
      ( ~ v1_xboole_0(X23)
      | v1_xboole_0(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f9746,f3253])).

fof(f9819,plain,
    ( spl33_108
    | spl33_56 ),
    inference(avatar_split_clause,[],[f9774,f4925,f9790])).

fof(f9774,plain,(
    ! [X22] :
      ( ~ v1_xboole_0(X22)
      | v1_xboole_0(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f9746,f3283])).

fof(f9818,plain,(
    spl33_112 ),
    inference(avatar_split_clause,[],[f9773,f9811])).

fof(f9773,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f9746,f2058])).

fof(f9817,plain,(
    spl33_112 ),
    inference(avatar_split_clause,[],[f9771,f9811])).

fof(f9771,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f9746,f2057])).

fof(f9816,plain,(
    spl33_112 ),
    inference(avatar_split_clause,[],[f9815,f9811])).

fof(f9815,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(global_subsumption,[],[f9766])).

fof(f9766,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(resolution,[],[f9746,f2075])).

fof(f9814,plain,(
    spl33_112 ),
    inference(avatar_split_clause,[],[f9766,f9811])).

fof(f9809,plain,(
    spl33_106 ),
    inference(avatar_split_clause,[],[f9764,f9782])).

fof(f9764,plain,(
    v1_relat_1(k3_tarski(k1_xboole_0)) ),
    inference(resolution,[],[f9746,f3351])).

fof(f9808,plain,
    ( spl33_108
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f9763,f2289,f2259,f9790])).

fof(f9763,plain,
    ( v1_xboole_0(k3_tarski(k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f9746,f6277])).

fof(f9807,plain,
    ( spl33_111
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f9762,f2259,f9804])).

fof(f9762,plain,
    ( v1_relat_1(k1_relat_1(k3_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(resolution,[],[f9746,f7349])).

fof(f9802,plain,
    ( spl33_56
    | spl33_106 ),
    inference(avatar_split_clause,[],[f9761,f9782,f4925])).

fof(f9761,plain,(
    ! [X14] :
      ( v1_relat_1(k3_tarski(k1_xboole_0))
      | ~ v1_xboole_0(X14) ) ),
    inference(resolution,[],[f9746,f3352])).

fof(f9801,plain,
    ( spl33_109
    | spl33_110 ),
    inference(avatar_split_clause,[],[f9760,f9799,f9795])).

fof(f9795,plain,
    ( spl33_109
  <=> v1_funct_1(k3_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_109])])).

fof(f9760,plain,(
    ! [X13] :
      ( ~ v1_funct_1(X13)
      | ~ v1_relat_1(X13)
      | v1_funct_1(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f9746,f3134])).

fof(f9793,plain,
    ( spl33_108
    | spl33_56 ),
    inference(avatar_split_clause,[],[f9757,f4925,f9790])).

fof(f9757,plain,(
    ! [X8] :
      ( ~ v1_xboole_0(X8)
      | v1_xboole_0(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f9746,f2782])).

fof(f9788,plain,
    ( spl33_106
    | spl33_107 ),
    inference(avatar_split_clause,[],[f9756,f9786,f9782])).

fof(f9756,plain,(
    ! [X7] :
      ( ~ v1_relat_1(X7)
      | v1_relat_1(k3_tarski(k1_xboole_0)) ) ),
    inference(resolution,[],[f9746,f2716])).

fof(f9745,plain,(
    spl33_105 ),
    inference(avatar_split_clause,[],[f9714,f9742])).

fof(f9742,plain,
    ( spl33_105
  <=> k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_105])])).

fof(f9714,plain,(
    k1_xboole_0 = k5_setfam_1(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f9664,f2075])).

fof(f9740,plain,(
    spl33_104 ),
    inference(avatar_split_clause,[],[f9712,f9737])).

fof(f9737,plain,
    ( spl33_104
  <=> v1_relat_1(k5_setfam_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_104])])).

fof(f9712,plain,(
    v1_relat_1(k5_setfam_1(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f9664,f3351])).

fof(f9735,plain,
    ( spl33_103
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f9711,f2289,f2259,f9732])).

fof(f9732,plain,
    ( spl33_103
  <=> v1_xboole_0(k5_setfam_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_103])])).

fof(f9711,plain,
    ( v1_xboole_0(k5_setfam_1(k1_xboole_0,k1_xboole_0))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f9664,f6277])).

fof(f9730,plain,
    ( spl33_102
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f9710,f2259,f9727])).

fof(f9727,plain,
    ( spl33_102
  <=> v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_102])])).

fof(f9710,plain,
    ( v1_relat_1(k1_relat_1(k5_setfam_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl33_4 ),
    inference(resolution,[],[f9664,f7349])).

fof(f9590,plain,
    ( ~ spl33_75
    | spl33_83 ),
    inference(avatar_contradiction_clause,[],[f9589])).

fof(f9589,plain,
    ( $false
    | ~ spl33_75
    | spl33_83 ),
    inference(subsumption_resolution,[],[f9554,f2237])).

fof(f9554,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl33_75
    | spl33_83 ),
    inference(superposition,[],[f7033,f6849])).

fof(f7033,plain,
    ( ~ r2_hidden(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))
    | spl33_83 ),
    inference(avatar_component_clause,[],[f7031])).

fof(f7031,plain,
    ( spl33_83
  <=> r2_hidden(k1_xboole_0,sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_83])])).

fof(f9477,plain,
    ( spl33_101
    | spl33_74 ),
    inference(avatar_split_clause,[],[f9472,f6843,f9474])).

fof(f6843,plain,
    ( spl33_74
  <=> r1_tarski(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_74])])).

fof(f9472,plain,
    ( k1_xboole_0 = sK28(k1_tarski(k1_xboole_0))
    | spl33_74 ),
    inference(subsumption_resolution,[],[f9441,f8902])).

fof(f9441,plain,
    ( ~ m1_subset_1(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))
    | k1_xboole_0 = sK28(k1_tarski(k1_xboole_0))
    | spl33_74 ),
    inference(resolution,[],[f3430,f6845])).

fof(f6845,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0)))
    | spl33_74 ),
    inference(avatar_component_clause,[],[f6843])).

fof(f3430,plain,(
    ! [X6,X7] :
      ( r1_tarski(k1_tarski(X7),X6)
      | ~ m1_subset_1(X7,X6)
      | k1_xboole_0 = X6 ) ),
    inference(resolution,[],[f2062,f2106])).

fof(f9091,plain,
    ( ~ spl33_100
    | spl33_1
    | spl33_40 ),
    inference(avatar_split_clause,[],[f9086,f3085,f2244,f9088])).

fof(f9086,plain,
    ( ~ v1_xboole_0(sK27(sK28(u1_pre_topc(sK2))))
    | spl33_1
    | spl33_40 ),
    inference(subsumption_resolution,[],[f9061,f3086])).

fof(f9061,plain,
    ( v1_xboole_0(u1_pre_topc(sK2))
    | ~ v1_xboole_0(sK27(sK28(u1_pre_topc(sK2))))
    | spl33_1 ),
    inference(resolution,[],[f8539,f2350])).

fof(f8849,plain,
    ( ~ spl33_99
    | spl33_98 ),
    inference(avatar_split_clause,[],[f8844,f8831,f8846])).

fof(f8844,plain,
    ( ~ v1_xboole_0(sK28(u1_pre_topc(sK2)))
    | spl33_98 ),
    inference(resolution,[],[f8833,f2517])).

fof(f2517,plain,(
    ! [X9] :
      ( v1_xboole_0(sK22(X9))
      | ~ v1_xboole_0(X9) ) ),
    inference(resolution,[],[f2141,f2108])).

fof(f2141,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1977])).

fof(f1977,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1851])).

fof(f1851,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f456])).

fof(f456,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f8834,plain,
    ( ~ spl33_98
    | spl33_1
    | spl33_40 ),
    inference(avatar_split_clause,[],[f8829,f3085,f2244,f8831])).

fof(f8829,plain,
    ( ~ v1_xboole_0(sK22(sK28(u1_pre_topc(sK2))))
    | spl33_1
    | spl33_40 ),
    inference(subsumption_resolution,[],[f8807,f3086])).

fof(f8807,plain,
    ( v1_xboole_0(u1_pre_topc(sK2))
    | ~ v1_xboole_0(sK22(sK28(u1_pre_topc(sK2))))
    | spl33_1 ),
    inference(resolution,[],[f8327,f2350])).

fof(f8664,plain,
    ( spl33_97
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8659,f2259,f8661])).

fof(f8659,plain,
    ( k1_xboole_0 = sK27(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f8646,f2261])).

fof(f8646,plain,(
    k1_xboole_0 = sK27(sK28(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f8542,f2075])).

fof(f8584,plain,
    ( spl33_96
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8579,f2259,f8581])).

fof(f8579,plain,
    ( v1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8538,f2161])).

fof(f8538,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(resolution,[],[f8304,f2702])).

fof(f8578,plain,
    ( spl33_95
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8573,f2259,f8575])).

fof(f8573,plain,
    ( r1_tarski(sK27(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8537,f2161])).

fof(f8537,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | r1_tarski(sK27(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f8304,f2469])).

fof(f8572,plain,
    ( spl33_94
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f8567,f2289,f2259,f8569])).

fof(f8567,plain,
    ( v1_xboole_0(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f8536,f2161])).

fof(f8536,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f8304,f2795])).

fof(f8566,plain,
    ( spl33_93
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8561,f2259,f8563])).

fof(f8561,plain,
    ( v1_relat_1(k1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8535,f2161])).

fof(f8535,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_relat_1(k1_relat_1(sK27(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f8304,f3505])).

fof(f8559,plain,
    ( spl33_92
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(avatar_split_clause,[],[f8554,f2337,f2324,f2259,f8556])).

fof(f8554,plain,
    ( v1_funct_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(subsumption_resolution,[],[f8533,f2161])).

fof(f8533,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_funct_1(sK27(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_16
    | ~ spl33_18 ),
    inference(resolution,[],[f8304,f3158])).

fof(f8481,plain,
    ( spl33_91
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8476,f2259,f8478])).

fof(f8476,plain,
    ( k1_xboole_0 = sK22(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f8464,f2261])).

fof(f8464,plain,(
    k1_xboole_0 = sK22(sK28(k1_zfmisc_1(k1_xboole_0))) ),
    inference(resolution,[],[f8330,f2075])).

fof(f8366,plain,
    ( spl33_90
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8361,f2259,f8363])).

fof(f8361,plain,
    ( v1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8326,f2161])).

fof(f8326,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4 ),
    inference(resolution,[],[f8303,f2702])).

fof(f8360,plain,
    ( spl33_89
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8355,f2259,f8357])).

fof(f8355,plain,
    ( r1_tarski(sK22(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8325,f2161])).

fof(f8325,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | r1_tarski(sK22(sK28(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f8303,f2469])).

fof(f8354,plain,
    ( spl33_88
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f8349,f2289,f2259,f8351])).

fof(f8349,plain,
    ( v1_xboole_0(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(subsumption_resolution,[],[f8324,f2161])).

fof(f8324,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_xboole_0(sK22(sK28(k1_tarski(k1_xboole_0))))
    | ~ spl33_4
    | ~ spl33_10 ),
    inference(resolution,[],[f8303,f2795])).

fof(f8348,plain,
    ( spl33_87
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f8343,f2259,f8345])).

fof(f8343,plain,
    ( v1_relat_1(k1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(subsumption_resolution,[],[f8323,f2161])).

fof(f8323,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | v1_relat_1(k1_relat_1(sK22(sK28(k1_tarski(k1_xboole_0)))))
    | ~ spl33_4 ),
    inference(resolution,[],[f8303,f3505])).

fof(f7763,plain,
    ( spl33_47
    | spl33_86 ),
    inference(avatar_split_clause,[],[f7742,f7761,f3401])).

fof(f7761,plain,
    ( spl33_86
  <=> ! [X25,X26] :
        ( r2_hidden(sK14(X25,k1_tarski(k1_xboole_0)),k1_zfmisc_1(X26))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_86])])).

fof(f7742,plain,(
    ! [X26,X25] :
      ( r2_hidden(sK14(X25,k1_tarski(k1_xboole_0)),k1_zfmisc_1(X26))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X25)) ) ),
    inference(resolution,[],[f2869,f2061])).

fof(f7759,plain,
    ( spl33_47
    | spl33_85 ),
    inference(avatar_split_clause,[],[f7741,f7757,f3401])).

fof(f7757,plain,
    ( spl33_85
  <=> ! [X23,X24] :
        ( r2_hidden(sK13(k1_tarski(k1_xboole_0),X23),k1_zfmisc_1(X24))
        | k1_tarski(k1_xboole_0) = k1_tarski(X23) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_85])])).

fof(f7741,plain,(
    ! [X24,X23] :
      ( r2_hidden(sK13(k1_tarski(k1_xboole_0),X23),k1_zfmisc_1(X24))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | k1_tarski(k1_xboole_0) = k1_tarski(X23) ) ),
    inference(resolution,[],[f2869,f2046])).

fof(f7755,plain,
    ( spl33_47
    | spl33_84 ),
    inference(avatar_split_clause,[],[f7740,f7753,f3401])).

fof(f7753,plain,
    ( spl33_84
  <=> ! [X22,X21] :
        ( r2_hidden(sK12(k1_tarski(k1_xboole_0),X21),k1_zfmisc_1(X22))
        | k1_tarski(k1_xboole_0) = k1_tarski(X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_84])])).

fof(f7740,plain,(
    ! [X21,X22] :
      ( r2_hidden(sK12(k1_tarski(k1_xboole_0),X21),k1_zfmisc_1(X22))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | k1_tarski(k1_xboole_0) = k1_tarski(X21) ) ),
    inference(resolution,[],[f2869,f2044])).

fof(f7034,plain,
    ( ~ spl33_83
    | spl33_74 ),
    inference(avatar_split_clause,[],[f7027,f6843,f7031])).

fof(f7027,plain,
    ( ~ r2_hidden(k1_xboole_0,sK28(k1_tarski(k1_xboole_0)))
    | spl33_74 ),
    inference(resolution,[],[f6845,f2174])).

fof(f6916,plain,
    ( spl33_47
    | spl33_82 ),
    inference(avatar_split_clause,[],[f6895,f6914,f3401])).

fof(f6914,plain,
    ( spl33_82
  <=> ! [X25,X26] :
        ( m1_subset_1(sK14(X25,k1_tarski(k1_xboole_0)),k1_zfmisc_1(X26))
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X25)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_82])])).

fof(f6895,plain,(
    ! [X26,X25] :
      ( m1_subset_1(sK14(X25,k1_tarski(k1_xboole_0)),k1_zfmisc_1(X26))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X25)) ) ),
    inference(resolution,[],[f3104,f2061])).

fof(f6912,plain,
    ( spl33_47
    | spl33_81 ),
    inference(avatar_split_clause,[],[f6894,f6910,f3401])).

fof(f6910,plain,
    ( spl33_81
  <=> ! [X23,X24] :
        ( m1_subset_1(sK13(k1_tarski(k1_xboole_0),X23),k1_zfmisc_1(X24))
        | k1_tarski(k1_xboole_0) = k1_tarski(X23) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_81])])).

fof(f6894,plain,(
    ! [X24,X23] :
      ( m1_subset_1(sK13(k1_tarski(k1_xboole_0),X23),k1_zfmisc_1(X24))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | k1_tarski(k1_xboole_0) = k1_tarski(X23) ) ),
    inference(resolution,[],[f3104,f2046])).

fof(f6908,plain,
    ( spl33_47
    | spl33_80 ),
    inference(avatar_split_clause,[],[f6893,f6906,f3401])).

fof(f6906,plain,
    ( spl33_80
  <=> ! [X22,X21] :
        ( m1_subset_1(sK12(k1_tarski(k1_xboole_0),X21),k1_zfmisc_1(X22))
        | k1_tarski(k1_xboole_0) = k1_tarski(X21) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_80])])).

fof(f6893,plain,(
    ! [X21,X22] :
      ( m1_subset_1(sK12(k1_tarski(k1_xboole_0),X21),k1_zfmisc_1(X22))
      | k1_xboole_0 = k1_tarski(k1_xboole_0)
      | k1_tarski(k1_xboole_0) = k1_tarski(X21) ) ),
    inference(resolution,[],[f3104,f2044])).

fof(f6876,plain,
    ( spl33_34
    | spl33_33 ),
    inference(avatar_split_clause,[],[f3462,f2729,f2732])).

fof(f6875,plain,
    ( spl33_33
    | spl33_78 ),
    inference(avatar_split_clause,[],[f3815,f6866,f2729])).

fof(f6874,plain,
    ( spl33_33
    | spl33_78 ),
    inference(avatar_split_clause,[],[f5481,f6866,f2729])).

fof(f5481,plain,(
    ! [X10,X11] :
      ( ~ v1_xboole_0(X10)
      | v1_relat_1(k1_tarski(X10))
      | ~ v1_relat_1(k1_zfmisc_1(X11)) ) ),
    inference(resolution,[],[f2376,f2110])).

fof(f6873,plain,
    ( ~ spl33_34
    | spl33_79
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6380,f2259,f6871,f2732])).

fof(f6380,plain,
    ( ! [X1] :
        ( v1_relat_1(k1_tarski(X1))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X1,k1_xboole_0) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2821,f2578])).

fof(f6869,plain,
    ( ~ spl33_34
    | spl33_78
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6381,f2259,f6866,f2732])).

fof(f6381,plain,
    ( ! [X2] :
        ( v1_relat_1(k1_tarski(X2))
        | ~ v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_xboole_0(X2) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2821,f2688])).

fof(f6868,plain,
    ( spl33_33
    | spl33_78 ),
    inference(avatar_split_clause,[],[f6383,f6866,f2729])).

fof(f6383,plain,(
    ! [X4,X5] :
      ( v1_relat_1(k1_tarski(X4))
      | ~ v1_relat_1(k1_zfmisc_1(X5))
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f2821,f2556])).

fof(f6864,plain,
    ( spl33_33
    | spl33_34 ),
    inference(avatar_split_clause,[],[f6385,f2732,f2729])).

fof(f6385,plain,(
    ! [X8] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(X8)) ) ),
    inference(resolution,[],[f2821,f2548])).

fof(f6863,plain,
    ( spl33_77
    | spl33_34
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6386,f2259,f2732,f6861])).

fof(f6861,plain,
    ( spl33_77
  <=> ! [X9] :
        ( ~ v1_relat_1(k1_tarski(X9))
        | ~ v1_xboole_0(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_77])])).

fof(f6386,plain,
    ( ! [X9] :
        ( v1_relat_1(k1_tarski(k1_xboole_0))
        | ~ v1_relat_1(k1_tarski(X9))
        | ~ v1_xboole_0(X9) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2821,f5537])).

fof(f6859,plain,
    ( spl33_33
    | spl33_34 ),
    inference(avatar_split_clause,[],[f6858,f2732,f2729])).

fof(f6858,plain,(
    ! [X1] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(X1)) ) ),
    inference(global_subsumption,[],[f2722])).

fof(f2722,plain,(
    ! [X10] :
      ( v1_relat_1(k1_tarski(k1_xboole_0))
      | ~ v1_relat_1(k1_zfmisc_1(X10)) ) ),
    inference(resolution,[],[f2110,f2077])).

fof(f6857,plain,
    ( spl33_76
    | ~ spl33_34
    | ~ spl33_72 ),
    inference(avatar_split_clause,[],[f6837,f6653,f2732,f6853])).

fof(f6853,plain,
    ( spl33_76
  <=> v1_relat_1(sK28(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_76])])).

fof(f6837,plain,
    ( ~ v1_relat_1(k1_tarski(k1_xboole_0))
    | v1_relat_1(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_72 ),
    inference(resolution,[],[f6655,f2716])).

fof(f6856,plain,
    ( spl33_76
    | ~ spl33_34
    | ~ spl33_72 ),
    inference(avatar_split_clause,[],[f6851,f6653,f2732,f6853])).

fof(f6851,plain,
    ( v1_relat_1(sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_34
    | ~ spl33_72 ),
    inference(subsumption_resolution,[],[f6837,f2734])).

fof(f6850,plain,
    ( ~ spl33_74
    | spl33_75
    | ~ spl33_72 ),
    inference(avatar_split_clause,[],[f6835,f6653,f6847,f6843])).

fof(f6835,plain,
    ( k1_tarski(k1_xboole_0) = sK28(k1_tarski(k1_xboole_0))
    | ~ r1_tarski(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_72 ),
    inference(resolution,[],[f6655,f2118])).

fof(f6691,plain,
    ( ~ spl33_73
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6685,f2259,f6688])).

fof(f6685,plain,
    ( ~ r2_hidden(k1_tarski(k1_xboole_0),sK28(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(superposition,[],[f6642,f2261])).

fof(f6642,plain,(
    ! [X0] : ~ r2_hidden(k1_zfmisc_1(X0),sK28(k1_tarski(X0))) ),
    inference(resolution,[],[f6621,f2010])).

fof(f6656,plain,
    ( spl33_72
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6650,f2259,f6653])).

fof(f6650,plain,
    ( r1_tarski(sK28(k1_tarski(k1_xboole_0)),k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(superposition,[],[f6621,f2261])).

fof(f6414,plain,
    ( spl33_70
    | spl33_71 ),
    inference(avatar_split_clause,[],[f6387,f6411,f6408])).

fof(f6408,plain,
    ( spl33_70
  <=> ! [X10] : ~ v1_relat_1(k1_zfmisc_1(k1_zfmisc_1(X10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_70])])).

fof(f6387,plain,(
    ! [X10] :
      ( v1_relat_1(k1_tarski(k1_tarski(k1_xboole_0)))
      | ~ v1_relat_1(k1_zfmisc_1(k1_zfmisc_1(X10))) ) ),
    inference(resolution,[],[f2821,f2767])).

fof(f6196,plain,
    ( spl33_47
    | spl33_69
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6178,f2259,f6194,f3401])).

fof(f6194,plain,
    ( spl33_69
  <=> ! [X13] :
        ( r1_tarski(sK14(X13,k1_tarski(k1_xboole_0)),k1_xboole_0)
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X13)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_69])])).

fof(f6178,plain,
    ( ! [X13] :
        ( r1_tarski(sK14(X13,k1_tarski(k1_xboole_0)),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(X13)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2600,f2061])).

fof(f6192,plain,
    ( spl33_47
    | spl33_68
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6177,f2259,f6190,f3401])).

fof(f6190,plain,
    ( spl33_68
  <=> ! [X12] :
        ( r1_tarski(sK13(k1_tarski(k1_xboole_0),X12),k1_xboole_0)
        | k1_tarski(k1_xboole_0) = k1_tarski(X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_68])])).

fof(f6177,plain,
    ( ! [X12] :
        ( r1_tarski(sK13(k1_tarski(k1_xboole_0),X12),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | k1_tarski(k1_xboole_0) = k1_tarski(X12) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2600,f2046])).

fof(f6188,plain,
    ( spl33_47
    | spl33_67
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f6176,f2259,f6186,f3401])).

fof(f6186,plain,
    ( spl33_67
  <=> ! [X11] :
        ( r1_tarski(sK12(k1_tarski(k1_xboole_0),X11),k1_xboole_0)
        | k1_tarski(k1_xboole_0) = k1_tarski(X11) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_67])])).

fof(f6176,plain,
    ( ! [X11] :
        ( r1_tarski(sK12(k1_tarski(k1_xboole_0),X11),k1_xboole_0)
        | k1_xboole_0 = k1_tarski(k1_xboole_0)
        | k1_tarski(k1_xboole_0) = k1_tarski(X11) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2600,f2044])).

fof(f5877,plain,
    ( spl33_66
    | ~ spl33_10
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f5872,f5757,f2289,f5874])).

fof(f5872,plain,
    ( v1_xboole_0(sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_10
    | ~ spl33_60 ),
    inference(subsumption_resolution,[],[f5854,f2291])).

fof(f5854,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2782])).

fof(f5871,plain,
    ( spl33_64
    | ~ spl33_10
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f5870,f5757,f2289,f5858])).

fof(f5870,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ spl33_10
    | ~ spl33_60 ),
    inference(subsumption_resolution,[],[f5852,f2291])).

fof(f5852,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2375])).

fof(f5869,plain,
    ( spl33_64
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f5868,f5757,f5858])).

fof(f5868,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ spl33_60 ),
    inference(subsumption_resolution,[],[f5851,f2079])).

fof(f5851,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2118])).

fof(f5866,plain,
    ( ~ spl33_65
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f5848,f5757,f5863])).

fof(f5863,plain,
    ( spl33_65
  <=> r2_hidden(k1_xboole_0,sK15(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_65])])).

fof(f5848,plain,
    ( ~ r2_hidden(k1_xboole_0,sK15(k1_tarski(k1_xboole_0)))
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2010])).

fof(f5861,plain,
    ( spl33_64
    | ~ spl33_60 ),
    inference(avatar_split_clause,[],[f5847,f5757,f5858])).

fof(f5847,plain,
    ( k1_xboole_0 = sK15(k1_tarski(k1_xboole_0))
    | ~ spl33_60 ),
    inference(resolution,[],[f5759,f2075])).

fof(f5827,plain,
    ( spl33_63
    | ~ spl33_10
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f5822,f5752,f2289,f5824])).

fof(f5822,plain,
    ( v1_xboole_0(sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_10
    | ~ spl33_59 ),
    inference(subsumption_resolution,[],[f5804,f2291])).

fof(f5804,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2782])).

fof(f5821,plain,
    ( spl33_61
    | ~ spl33_10
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f5820,f5752,f2289,f5808])).

fof(f5820,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ spl33_10
    | ~ spl33_59 ),
    inference(subsumption_resolution,[],[f5802,f2291])).

fof(f5802,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2375])).

fof(f5819,plain,
    ( spl33_61
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f5818,f5752,f5808])).

fof(f5818,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ spl33_59 ),
    inference(subsumption_resolution,[],[f5801,f2079])).

fof(f5801,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ r1_tarski(k1_xboole_0,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2118])).

fof(f5816,plain,
    ( ~ spl33_62
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f5798,f5752,f5813])).

fof(f5813,plain,
    ( spl33_62
  <=> r2_hidden(k1_xboole_0,sK3(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_62])])).

fof(f5798,plain,
    ( ~ r2_hidden(k1_xboole_0,sK3(k1_tarski(k1_xboole_0)))
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2010])).

fof(f5811,plain,
    ( spl33_61
    | ~ spl33_59 ),
    inference(avatar_split_clause,[],[f5797,f5752,f5808])).

fof(f5797,plain,
    ( k1_xboole_0 = sK3(k1_tarski(k1_xboole_0))
    | ~ spl33_59 ),
    inference(resolution,[],[f5754,f2075])).

fof(f5782,plain,(
    ~ spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5781])).

fof(f5781,plain,
    ( $false
    | ~ spl33_45 ),
    inference(subsumption_resolution,[],[f5773,f2161])).

fof(f5773,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl33_45 ),
    inference(resolution,[],[f3394,f2146])).

fof(f3394,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_tarski(k1_xboole_0))
    | ~ spl33_45 ),
    inference(avatar_component_clause,[],[f3393])).

fof(f3393,plain,
    ( spl33_45
  <=> ! [X1] : ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_45])])).

fof(f5780,plain,(
    ~ spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5779])).

fof(f5779,plain,
    ( $false
    | ~ spl33_45 ),
    inference(subsumption_resolution,[],[f5772,f2161])).

fof(f5772,plain,
    ( v1_xboole_0(k1_tarski(k1_xboole_0))
    | ~ spl33_45 ),
    inference(resolution,[],[f3394,f2761])).

fof(f5778,plain,
    ( ~ spl33_4
    | ~ spl33_10
    | ~ spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5777])).

fof(f5777,plain,
    ( $false
    | ~ spl33_4
    | ~ spl33_10
    | ~ spl33_45 ),
    inference(subsumption_resolution,[],[f5763,f2291])).

fof(f5763,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl33_4
    | ~ spl33_45 ),
    inference(resolution,[],[f3394,f5537])).

fof(f5776,plain,(
    ~ spl33_45 ),
    inference(avatar_contradiction_clause,[],[f5762])).

fof(f5762,plain,
    ( $false
    | ~ spl33_45 ),
    inference(resolution,[],[f3394,f2237])).

fof(f5760,plain,
    ( spl33_47
    | spl33_60
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f5746,f2259,f5757,f3401])).

fof(f5746,plain,
    ( r1_tarski(sK15(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f2469,f2456])).

fof(f2456,plain,(
    ! [X1] :
      ( m1_subset_1(sK15(X1),X1)
      | k1_xboole_0 = X1 ) ),
    inference(resolution,[],[f2066,f2034])).

fof(f5755,plain,
    ( spl33_45
    | spl33_59
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f5740,f2259,f5752,f3393])).

fof(f5740,plain,
    ( ! [X2] :
        ( r1_tarski(sK3(k1_tarski(k1_xboole_0)),k1_xboole_0)
        | ~ r2_hidden(X2,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2469,f2447])).

fof(f2447,plain,(
    ! [X2,X3] :
      ( m1_subset_1(sK3(X3),X3)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f2008,f2034])).

fof(f5350,plain,
    ( ~ spl33_10
    | ~ spl33_56 ),
    inference(avatar_contradiction_clause,[],[f5335])).

fof(f5335,plain,
    ( $false
    | ~ spl33_10
    | ~ spl33_56 ),
    inference(resolution,[],[f4926,f2291])).

fof(f4926,plain,
    ( ! [X7] : ~ v1_xboole_0(X7)
    | ~ spl33_56 ),
    inference(avatar_component_clause,[],[f4925])).

fof(f5349,plain,
    ( ~ spl33_8
    | ~ spl33_56 ),
    inference(avatar_contradiction_clause,[],[f5344])).

fof(f5344,plain,
    ( $false
    | ~ spl33_8
    | ~ spl33_56 ),
    inference(resolution,[],[f4926,f2281])).

fof(f2281,plain,
    ( v1_xboole_0(sK24)
    | ~ spl33_8 ),
    inference(avatar_component_clause,[],[f2279])).

fof(f2279,plain,
    ( spl33_8
  <=> v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_8])])).

fof(f5348,plain,(
    ~ spl33_56 ),
    inference(avatar_contradiction_clause,[],[f5345])).

fof(f5345,plain,
    ( $false
    | ~ spl33_56 ),
    inference(resolution,[],[f4926,f2144])).

fof(f5331,plain,
    ( spl33_56
    | spl33_58
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f5327,f2259,f5329,f4925])).

fof(f5329,plain,
    ( spl33_58
  <=> ! [X11,X13,X10,X12] :
        ( ~ m1_subset_1(X11,k1_tarski(k1_xboole_0))
        | m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
        | ~ r1_tarski(X10,X12) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_58])])).

fof(f5327,plain,
    ( ! [X12,X10,X13,X11,X9] :
        ( ~ m1_subset_1(X11,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(X10,X12)
        | m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
        | ~ v1_xboole_0(X9) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f5326,f2261])).

fof(f5326,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X10,X12)
      | m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ v1_xboole_0(X9) ) ),
    inference(subsumption_resolution,[],[f5317,f2348])).

fof(f2348,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f2079,f2152])).

fof(f5317,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(X10,X12)
      | ~ r1_tarski(X9,X13)
      | m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(X13,X12)))
      | ~ v1_xboole_0(X9) ) ),
    inference(superposition,[],[f2103,f3714])).

fof(f4930,plain,
    ( spl33_56
    | spl33_57
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f4923,f2259,f4928,f4925])).

fof(f4928,plain,
    ( spl33_57
  <=> ! [X9,X8,X10] :
        ( ~ m1_subset_1(X9,k1_tarski(k1_xboole_0))
        | m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
        | ~ r1_tarski(k1_relat_1(X9),X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_57])])).

fof(f4923,plain,
    ( ! [X10,X8,X7,X9] :
        ( ~ m1_subset_1(X9,k1_tarski(k1_xboole_0))
        | ~ r1_tarski(k1_relat_1(X9),X10)
        | m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
        | ~ v1_xboole_0(X7) )
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f4914,f2261])).

fof(f4914,plain,(
    ! [X10,X8,X7,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(X9),X10)
      | m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X8)))
      | ~ v1_xboole_0(X7) ) ),
    inference(superposition,[],[f2202,f3714])).

fof(f2202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f1887])).

fof(f1887,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1886])).

fof(f1886,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1241])).

fof(f1241,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f3793,plain,
    ( spl33_55
    | spl33_38
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3785,f2244,f3076,f3791])).

fof(f3791,plain,
    ( spl33_55
  <=> ! [X28] :
        ( ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X28))
        | ~ v1_xboole_0(sK14(X28,u1_pre_topc(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_55])])).

fof(f3785,plain,
    ( ! [X28] :
        ( k1_xboole_0 = u1_pre_topc(sK2)
        | ~ m1_subset_1(u1_pre_topc(sK2),k1_zfmisc_1(X28))
        | ~ v1_xboole_0(sK14(X28,u1_pre_topc(sK2))) )
    | spl33_1 ),
    inference(resolution,[],[f2061,f2350])).

fof(f3690,plain,
    ( spl33_54
    | spl33_38
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3684,f2244,f3076,f3688])).

fof(f3688,plain,
    ( spl33_54
  <=> ! [X22] :
        ( u1_pre_topc(sK2) = k1_tarski(X22)
        | ~ v1_xboole_0(sK13(u1_pre_topc(sK2),X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_54])])).

fof(f3684,plain,
    ( ! [X22] :
        ( k1_xboole_0 = u1_pre_topc(sK2)
        | u1_pre_topc(sK2) = k1_tarski(X22)
        | ~ v1_xboole_0(sK13(u1_pre_topc(sK2),X22)) )
    | spl33_1 ),
    inference(resolution,[],[f2046,f2350])).

fof(f3670,plain,
    ( ~ spl33_2
    | ~ spl33_3
    | ~ spl33_40 ),
    inference(avatar_contradiction_clause,[],[f3669])).

fof(f3669,plain,
    ( $false
    | ~ spl33_2
    | ~ spl33_3
    | ~ spl33_40 ),
    inference(subsumption_resolution,[],[f3668,f2256])).

fof(f2256,plain,
    ( v2_pre_topc(sK2)
    | ~ spl33_3 ),
    inference(avatar_component_clause,[],[f2254])).

fof(f2254,plain,
    ( spl33_3
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_3])])).

fof(f3668,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ spl33_2
    | ~ spl33_40 ),
    inference(subsumption_resolution,[],[f3663,f2251])).

fof(f2251,plain,
    ( l1_pre_topc(sK2)
    | ~ spl33_2 ),
    inference(avatar_component_clause,[],[f2249])).

fof(f2249,plain,
    ( spl33_2
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_2])])).

fof(f3663,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl33_40 ),
    inference(resolution,[],[f3087,f2037])).

fof(f2037,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1796])).

fof(f1796,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1795])).

fof(f1795,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1766])).

fof(f1766,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ~ v1_xboole_0(u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_pre_topc)).

fof(f3087,plain,
    ( v1_xboole_0(u1_pre_topc(sK2))
    | ~ spl33_40 ),
    inference(avatar_component_clause,[],[f3085])).

fof(f3667,plain,
    ( ~ spl33_19
    | ~ spl33_40 ),
    inference(avatar_contradiction_clause,[],[f3666])).

fof(f3666,plain,
    ( $false
    | ~ spl33_19
    | ~ spl33_40 ),
    inference(subsumption_resolution,[],[f3662,f2383])).

fof(f3662,plain,
    ( ~ sP0(sK2)
    | ~ spl33_40 ),
    inference(resolution,[],[f3087,f2461])).

fof(f2461,plain,(
    ! [X2] :
      ( ~ v1_xboole_0(u1_pre_topc(X2))
      | ~ sP0(X2) ) ),
    inference(resolution,[],[f2084,f2126])).

fof(f2126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f1837])).

fof(f1837,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f148])).

fof(f148,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f2084,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f1965])).

fof(f3661,plain,
    ( spl33_53
    | spl33_38
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3655,f2244,f3076,f3659])).

fof(f3659,plain,
    ( spl33_53
  <=> ! [X22] :
        ( u1_pre_topc(sK2) = k1_tarski(X22)
        | ~ v1_xboole_0(sK12(u1_pre_topc(sK2),X22)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_53])])).

fof(f3655,plain,
    ( ! [X22] :
        ( k1_xboole_0 = u1_pre_topc(sK2)
        | u1_pre_topc(sK2) = k1_tarski(X22)
        | ~ v1_xboole_0(sK12(u1_pre_topc(sK2),X22)) )
    | spl33_1 ),
    inference(resolution,[],[f2044,f2350])).

fof(f3644,plain,
    ( ~ spl33_52
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3639,f2259,f3641])).

fof(f3639,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f3633,f2261])).

fof(f3631,plain,
    ( ~ spl33_51
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3626,f2259,f3628])).

fof(f3626,plain,
    ( ~ r1_tarski(k1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f3586,f2261])).

fof(f3609,plain,
    ( ~ spl33_50
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3604,f2259,f3606])).

fof(f3604,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f3574,f2261])).

fof(f3584,plain,
    ( ~ spl33_49
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3579,f2259,f3581])).

fof(f3579,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(k1_tarski(k1_xboole_0))),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f3557,f2261])).

fof(f3408,plain,
    ( spl33_47
    | spl33_48
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3387,f2259,f3405,f3401])).

fof(f3387,plain,
    ( v1_relat_1(sK15(k1_tarski(k1_xboole_0)))
    | k1_xboole_0 = k1_tarski(k1_xboole_0)
    | ~ spl33_4 ),
    inference(resolution,[],[f2702,f2456])).

fof(f3399,plain,
    ( spl33_45
    | spl33_46
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f3386,f2259,f3396,f3393])).

fof(f3386,plain,
    ( ! [X1] :
        ( v1_relat_1(sK3(k1_tarski(k1_xboole_0)))
        | ~ r2_hidden(X1,k1_tarski(k1_xboole_0)) )
    | ~ spl33_4 ),
    inference(resolution,[],[f2702,f2447])).

fof(f3155,plain,
    ( spl33_43
    | spl33_44 ),
    inference(avatar_split_clause,[],[f3140,f3152,f3149])).

fof(f3140,plain,(
    ! [X10] :
      ( v1_funct_1(k1_tarski(k1_xboole_0))
      | ~ v1_funct_1(k1_zfmisc_1(X10))
      | ~ v1_relat_1(k1_zfmisc_1(X10)) ) ),
    inference(resolution,[],[f2109,f2077])).

fof(f3119,plain,
    ( ~ spl33_40
    | spl33_41 ),
    inference(avatar_split_clause,[],[f3118,f3089,f3085])).

fof(f3118,plain,
    ( ~ v1_xboole_0(u1_pre_topc(sK2))
    | spl33_41 ),
    inference(resolution,[],[f3091,f2517])).

fof(f3097,plain,
    ( spl33_40
    | ~ spl33_42
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3060,f2244,f3094,f3085])).

fof(f3060,plain,
    ( ~ v1_xboole_0(sK27(u1_pre_topc(sK2)))
    | v1_xboole_0(u1_pre_topc(sK2))
    | spl33_1 ),
    inference(resolution,[],[f2350,f2146])).

fof(f3092,plain,
    ( spl33_40
    | ~ spl33_41
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3059,f2244,f3089,f3085])).

fof(f3059,plain,
    ( ~ v1_xboole_0(sK22(u1_pre_topc(sK2)))
    | v1_xboole_0(u1_pre_topc(sK2))
    | spl33_1 ),
    inference(resolution,[],[f2350,f2761])).

fof(f3083,plain,
    ( spl33_38
    | ~ spl33_39
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3058,f2244,f3080,f3076])).

fof(f3058,plain,
    ( ~ v1_xboole_0(sK15(u1_pre_topc(sK2)))
    | k1_xboole_0 = u1_pre_topc(sK2)
    | spl33_1 ),
    inference(resolution,[],[f2350,f2066])).

fof(f3074,plain,
    ( spl33_36
    | ~ spl33_37
    | spl33_1 ),
    inference(avatar_split_clause,[],[f3056,f2244,f3071,f3068])).

fof(f3068,plain,
    ( spl33_36
  <=> ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_36])])).

fof(f3056,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK3(u1_pre_topc(sK2)))
        | ~ r2_hidden(X0,u1_pre_topc(sK2)) )
    | spl33_1 ),
    inference(resolution,[],[f2350,f2008])).

fof(f3066,plain,
    ( ~ spl33_35
    | spl33_1
    | ~ spl33_19 ),
    inference(avatar_split_clause,[],[f3061,f2381,f2244,f3063])).

fof(f3061,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl33_1
    | ~ spl33_19 ),
    inference(subsumption_resolution,[],[f3055,f2383])).

fof(f3055,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ sP0(sK2)
    | spl33_1 ),
    inference(resolution,[],[f2350,f2084])).

fof(f2735,plain,
    ( spl33_33
    | spl33_34 ),
    inference(avatar_split_clause,[],[f2722,f2732,f2729])).

fof(f2607,plain,
    ( ~ spl33_32
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2602,f2259,f2604])).

fof(f2602,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f2577,f2261])).

fof(f2593,plain,
    ( ~ spl33_31
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2588,f2259,f2590])).

fof(f2588,plain,
    ( ~ r1_tarski(k1_tarski(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f2576,f2261])).

fof(f2585,plain,
    ( ~ spl33_30
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2580,f2259,f2582])).

fof(f2580,plain,
    ( ~ r1_tarski(k1_tarski(k1_xboole_0),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f2572,f2261])).

fof(f2510,plain,
    ( spl33_29
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2499,f2259,f2507])).

fof(f2499,plain,
    ( r1_tarski(sK27(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f2470,f2261])).

fof(f2505,plain,
    ( spl33_28
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2500,f2259,f2502])).

fof(f2502,plain,
    ( spl33_28
  <=> k1_xboole_0 = sK27(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_28])])).

fof(f2500,plain,
    ( k1_xboole_0 = sK27(k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f2498,f2261])).

fof(f2498,plain,(
    k1_xboole_0 = sK27(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f2470,f2075])).

fof(f2496,plain,
    ( spl33_27
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2485,f2259,f2493])).

fof(f2485,plain,
    ( r1_tarski(sK22(k1_tarski(k1_xboole_0)),k1_xboole_0)
    | ~ spl33_4 ),
    inference(superposition,[],[f2466,f2261])).

fof(f2491,plain,
    ( spl33_26
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2486,f2259,f2488])).

fof(f2488,plain,
    ( spl33_26
  <=> k1_xboole_0 = sK22(k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_26])])).

fof(f2486,plain,
    ( k1_xboole_0 = sK22(k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(forward_demodulation,[],[f2484,f2261])).

fof(f2484,plain,(
    k1_xboole_0 = sK22(k1_zfmisc_1(k1_xboole_0)) ),
    inference(resolution,[],[f2466,f2075])).

fof(f2477,plain,(
    spl33_25 ),
    inference(avatar_split_clause,[],[f2472,f2474])).

fof(f2474,plain,
    ( spl33_25
  <=> k1_xboole_0 = sK26(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_25])])).

fof(f2472,plain,(
    k1_xboole_0 = sK26(k1_xboole_0) ),
    inference(resolution,[],[f2467,f2075])).

fof(f2440,plain,
    ( spl33_24
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2428,f2259,f2437])).

fof(f2437,plain,
    ( spl33_24
  <=> m1_subset_1(sK26(k1_xboole_0),k1_tarski(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_24])])).

fof(f2428,plain,
    ( m1_subset_1(sK26(k1_xboole_0),k1_tarski(k1_xboole_0))
    | ~ spl33_4 ),
    inference(superposition,[],[f2143,f2261])).

fof(f2435,plain,
    ( spl33_23
    | ~ spl33_4 ),
    inference(avatar_split_clause,[],[f2425,f2259,f2432])).

fof(f2432,plain,
    ( spl33_23
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_23])])).

fof(f2425,plain,
    ( m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_tarski(k1_xboole_0)))
    | ~ spl33_4 ),
    inference(superposition,[],[f2077,f2261])).

fof(f2419,plain,(
    spl33_22 ),
    inference(avatar_split_clause,[],[f2414,f2416])).

fof(f2416,plain,
    ( spl33_22
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_22])])).

fof(f2414,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f2411,f2229])).

fof(f2411,plain,(
    ! [X2] : k1_xboole_0 = k1_relat_1(k2_zfmisc_1(k1_xboole_0,X2)) ),
    inference(resolution,[],[f2203,f2075])).

fof(f2397,plain,
    ( ~ spl33_20
    | ~ spl33_14
    | spl33_21 ),
    inference(avatar_split_clause,[],[f2396,f2390,f2311,f2386])).

fof(f2386,plain,
    ( spl33_20
  <=> sP0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_20])])).

fof(f2311,plain,
    ( spl33_14
  <=> sP1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_14])])).

fof(f2390,plain,
    ( spl33_21
  <=> v2_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_21])])).

fof(f2396,plain,
    ( ~ sP0(sK18)
    | ~ spl33_14
    | spl33_21 ),
    inference(subsumption_resolution,[],[f2395,f2392])).

fof(f2392,plain,
    ( ~ v2_pre_topc(sK18)
    | spl33_21 ),
    inference(avatar_component_clause,[],[f2390])).

fof(f2395,plain,
    ( ~ sP0(sK18)
    | v2_pre_topc(sK18)
    | ~ spl33_14 ),
    inference(resolution,[],[f2083,f2313])).

fof(f2313,plain,
    ( sP1(sK18)
    | ~ spl33_14 ),
    inference(avatar_component_clause,[],[f2311])).

fof(f2083,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ sP0(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1958])).

fof(f1958,plain,(
    ! [X0] :
      ( ( ( v2_pre_topc(X0)
          | ~ sP0(X0) )
        & ( sP0(X0)
          | ~ v2_pre_topc(X0) ) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f1908])).

fof(f1908,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> sP0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2393,plain,
    ( spl33_20
    | ~ spl33_21
    | ~ spl33_14 ),
    inference(avatar_split_clause,[],[f2378,f2311,f2390,f2386])).

fof(f2378,plain,
    ( ~ v2_pre_topc(sK18)
    | sP0(sK18)
    | ~ spl33_14 ),
    inference(resolution,[],[f2082,f2313])).

fof(f2082,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | ~ v2_pre_topc(X0)
      | sP0(X0) ) ),
    inference(cnf_transformation,[],[f1958])).

fof(f2384,plain,
    ( spl33_19
    | ~ spl33_3
    | ~ spl33_13 ),
    inference(avatar_split_clause,[],[f2379,f2306,f2254,f2381])).

fof(f2306,plain,
    ( spl33_13
  <=> sP1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_13])])).

fof(f2379,plain,
    ( sP0(sK2)
    | ~ spl33_3
    | ~ spl33_13 ),
    inference(subsumption_resolution,[],[f2377,f2256])).

fof(f2377,plain,
    ( ~ v2_pre_topc(sK2)
    | sP0(sK2)
    | ~ spl33_13 ),
    inference(resolution,[],[f2082,f2308])).

fof(f2308,plain,
    ( sP1(sK2)
    | ~ spl33_13 ),
    inference(avatar_component_clause,[],[f2306])).

fof(f2340,plain,
    ( spl33_18
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f2330,f2289,f2337])).

fof(f2330,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl33_10 ),
    inference(resolution,[],[f2155,f2291])).

fof(f2335,plain,
    ( spl33_17
    | ~ spl33_8 ),
    inference(avatar_split_clause,[],[f2329,f2279,f2332])).

fof(f2329,plain,
    ( v1_funct_1(sK24)
    | ~ spl33_8 ),
    inference(resolution,[],[f2155,f2281])).

fof(f2327,plain,
    ( spl33_16
    | ~ spl33_10 ),
    inference(avatar_split_clause,[],[f2317,f2289,f2324])).

fof(f2317,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl33_10 ),
    inference(resolution,[],[f2154,f2291])).

fof(f2322,plain,
    ( spl33_15
    | ~ spl33_8 ),
    inference(avatar_split_clause,[],[f2316,f2279,f2319])).

fof(f2316,plain,
    ( v1_relat_1(sK24)
    | ~ spl33_8 ),
    inference(resolution,[],[f2154,f2281])).

fof(f2314,plain,
    ( spl33_14
    | ~ spl33_5 ),
    inference(avatar_split_clause,[],[f2304,f2264,f2311])).

fof(f2264,plain,
    ( spl33_5
  <=> l1_pre_topc(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_5])])).

fof(f2304,plain,
    ( sP1(sK18)
    | ~ spl33_5 ),
    inference(resolution,[],[f2102,f2266])).

fof(f2266,plain,
    ( l1_pre_topc(sK18)
    | ~ spl33_5 ),
    inference(avatar_component_clause,[],[f2264])).

fof(f2102,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | sP1(X0) ) ),
    inference(cnf_transformation,[],[f1909])).

fof(f1909,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f1820,f1908,f1907])).

fof(f1820,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1819])).

fof(f1819,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1769])).

fof(f1769,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f2309,plain,
    ( spl33_13
    | ~ spl33_2 ),
    inference(avatar_split_clause,[],[f2303,f2249,f2306])).

fof(f2303,plain,
    ( sP1(sK2)
    | ~ spl33_2 ),
    inference(resolution,[],[f2102,f2251])).

fof(f2302,plain,(
    spl33_12 ),
    inference(avatar_split_clause,[],[f2206,f2299])).

fof(f2206,plain,(
    v1_relat_1(sK31) ),
    inference(cnf_transformation,[],[f1995])).

fof(f1995,plain,
    ( v1_funct_1(sK31)
    & v1_relat_1(sK31) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK31])],[f930,f1994])).

fof(f1994,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK31)
      & v1_relat_1(sK31) ) ),
    introduced(choice_axiom,[])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f2297,plain,(
    spl33_11 ),
    inference(avatar_split_clause,[],[f2207,f2294])).

fof(f2207,plain,(
    v1_funct_1(sK31) ),
    inference(cnf_transformation,[],[f1995])).

fof(f2292,plain,(
    spl33_10 ),
    inference(avatar_split_clause,[],[f2162,f2289])).

fof(f2162,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f2287,plain,(
    ~ spl33_9 ),
    inference(avatar_split_clause,[],[f2124,f2284])).

fof(f2124,plain,(
    ~ v1_xboole_0(sK25) ),
    inference(cnf_transformation,[],[f1976])).

fof(f1976,plain,(
    ~ v1_xboole_0(sK25) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f27,f1975])).

fof(f1975,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK25) ),
    introduced(choice_axiom,[])).

fof(f27,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_xboole_0)).

fof(f2282,plain,(
    spl33_8 ),
    inference(avatar_split_clause,[],[f2123,f2279])).

fof(f2123,plain,(
    v1_xboole_0(sK24) ),
    inference(cnf_transformation,[],[f1974])).

fof(f1974,plain,(
    v1_xboole_0(sK24) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f26,f1973])).

fof(f1973,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK24) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f2277,plain,(
    ~ spl33_7 ),
    inference(avatar_split_clause,[],[f2121,f2274])).

fof(f2121,plain,(
    ~ v1_xboole_0(sK23) ),
    inference(cnf_transformation,[],[f1972])).

fof(f1972,plain,
    ( v1_relat_1(sK23)
    & ~ v1_xboole_0(sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f702,f1971])).

fof(f1971,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK23)
      & ~ v1_xboole_0(sK23) ) ),
    introduced(choice_axiom,[])).

fof(f702,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f2272,plain,(
    spl33_6 ),
    inference(avatar_split_clause,[],[f2122,f2269])).

fof(f2269,plain,
    ( spl33_6
  <=> v1_relat_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl33_6])])).

fof(f2122,plain,(
    v1_relat_1(sK23) ),
    inference(cnf_transformation,[],[f1972])).

fof(f2267,plain,(
    spl33_5 ),
    inference(avatar_split_clause,[],[f2081,f2264])).

fof(f2081,plain,(
    l1_pre_topc(sK18) ),
    inference(cnf_transformation,[],[f1957])).

fof(f1957,plain,(
    l1_pre_topc(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f1764,f1956])).

fof(f1956,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK18) ),
    introduced(choice_axiom,[])).

fof(f1764,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_l1_pre_topc)).

fof(f2262,plain,(
    spl33_4 ),
    inference(avatar_split_clause,[],[f2080,f2259])).

fof(f2080,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f376])).

fof(f376,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f2257,plain,(
    spl33_3 ),
    inference(avatar_split_clause,[],[f2000,f2254])).

fof(f2000,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f1911])).

fof(f1911,plain,
    ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK2))
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f1771,f1910])).

fof(f1910,plain,
    ( ? [X0] :
        ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK2))
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f1771,plain,(
    ? [X0] :
      ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1770])).

fof(f1770,plain,(
    ? [X0] :
      ( ~ r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1768])).

fof(f1768,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    inference(negated_conjecture,[],[f1767])).

fof(f1767,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f2252,plain,(
    spl33_2 ),
    inference(avatar_split_clause,[],[f2001,f2249])).

fof(f2001,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f1911])).

fof(f2247,plain,(
    ~ spl33_1 ),
    inference(avatar_split_clause,[],[f2002,f2244])).

fof(f2002,plain,(
    ~ r2_hidden(k1_xboole_0,u1_pre_topc(sK2)) ),
    inference(cnf_transformation,[],[f1911])).
%------------------------------------------------------------------------------
