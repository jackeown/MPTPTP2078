%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0831+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:50 EST 2020

% Result     : Theorem 16.82s
% Output     : Refutation 17.78s
% Verified   : 
% Statistics : Number of formulae       : 4560 (23332 expanded)
%              Number of leaves         :  920 (9792 expanded)
%              Depth                    :   11
%              Number of atoms          : 10522 (60744 expanded)
%              Number of equality atoms : 1503 (10330 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32331,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f5105,f5110,f5115,f6975,f6980,f6985,f6986,f6991,f7013,f7039,f7044,f7055,f7060,f7061,f7064,f7066,f7068,f7076,f7083,f7089,f7091,f7093,f7095,f7096,f7097,f7318,f7323,f7328,f7329,f7334,f7344,f7350,f7356,f7376,f7384,f7391,f7397,f7399,f7401,f7403,f7404,f7405,f7411,f7416,f7421,f7426,f7431,f7436,f7441,f7474,f7475,f7476,f7479,f7480,f7481,f7488,f7493,f7498,f7531,f7532,f7533,f7536,f7537,f7538,f7545,f7550,f7555,f7562,f7567,f7572,f7578,f7583,f7588,f7619,f7620,f7621,f7624,f7625,f7626,f7629,f7630,f7631,f7632,f7638,f7647,f7658,f7666,f7678,f7706,f7707,f7712,f7717,f7722,f7727,f7732,f7737,f7744,f7749,f7754,f7759,f7764,f7769,f7801,f7802,f7803,f7806,f7807,f7808,f7811,f7812,f7813,f7814,f7820,f7829,f7842,f7855,f7868,f7873,f7878,f7879,f7937,f7946,f7955,f7960,f7965,f7966,f8028,f8033,f8038,f8043,f8048,f8053,f8329,f8334,f8336,f8338,f8341,f8430,f8444,f8449,f8455,f8464,f8485,f8488,f8493,f8495,f8497,f8498,f8499,f8500,f8517,f8524,f8531,f8536,f8541,f8654,f8655,f8660,f8665,f8670,f8675,f8680,f8685,f8690,f8696,f8697,f8702,f8707,f8708,f8714,f8715,f8720,f8725,f8726,f8731,f8736,f8737,f8738,f8743,f8748,f8749,f8750,f8755,f8760,f8765,f8770,f8775,f8776,f8782,f8787,f8792,f8793,f8798,f8803,f8808,f8809,f8814,f8819,f8820,f8825,f8830,f8831,f8836,f8841,f8842,f8847,f8848,f8856,f8860,f20614,f20620,f20626,f20657,f20662,f20667,f20692,f20699,f20706,f20743,f20744,f20745,f20746,f20755,f20770,f20777,f20784,f20818,f20819,f20820,f20821,f20827,f20833,f20848,f20855,f20862,f20899,f20900,f20901,f20902,f20911,f20926,f20933,f20940,f20988,f20989,f20990,f20991,f21011,f21202,f21209,f21216,f21235,f21256,f21271,f21278,f21285,f21304,f21325,f21340,f21347,f21354,f21373,f21394,f21993,f21998,f22003,f22008,f22013,f22014,f22015,f22016,f22017,f22018,f22019,f22020,f22021,f22022,f22023,f22024,f22025,f22026,f22027,f22028,f22061,f22064,f22067,f22082,f22099,f22147,f22154,f22157,f22164,f22165,f22173,f22176,f22183,f22184,f22185,f22189,f22196,f22257,f22258,f22259,f22263,f22337,f22338,f22339,f22340,f22353,f22359,f22365,f22384,f22385,f22386,f22387,f22390,f22405,f22412,f22419,f22453,f22454,f22455,f22655,f22662,f22669,f22688,f22709,f22724,f22731,f22738,f22757,f22778,f22793,f22800,f22807,f22826,f22847,f23473,f23479,f23485,f23497,f23510,f23511,f23512,f23513,f23514,f23515,f23516,f23517,f23518,f23519,f23520,f23521,f23522,f23523,f23524,f23525,f23585,f23589,f23593,f23615,f23640,f23693,f23700,f23703,f23711,f23712,f23721,f23724,f23732,f23733,f23734,f23739,f23747,f23814,f23815,f23816,f23822,f23905,f23907,f23909,f23917,f23931,f23936,f23951,f23958,f23965,f24002,f24003,f24004,f24031,f24038,f24045,f24094,f24095,f24096,f24125,f24130,f24131,f24136,f24137,f24142,f24147,f24148,f24153,f24154,f24155,f24170,f24177,f24184,f24203,f24240,f24247,f24254,f24269,f24305,f24312,f24319,f24347,f24384,f24391,f24398,f24422,f24634,f24641,f24648,f24667,f24688,f24703,f24710,f24717,f24736,f24757,f24772,f24779,f24786,f24805,f24826,f25105,f25112,f25119,f25138,f25159,f25724,f25731,f25738,f25757,f25778,f25793,f25800,f25807,f25826,f25847,f25862,f25869,f25876,f25895,f25916,f26191,f26194,f26197,f26212,f26229,f26798,f26805,f26812,f26827,f26859,f26866,f26873,f26888,f26920,f26927,f26934,f26949,f27247,f27250,f27253,f27268,f27677,f27734,f27739,f27744,f27749,f27759,f27765,f27771,f27783,f27813,f27819,f27825,f27833,f27857,f27862,f27867,f27872,f27882,f27887,f27892,f27897,f27898,f27908,f27913,f27918,f27923,f27928,f27935,f27940,f27945,f27950,f27951,f27956,f27961,f27968,f27973,f27978,f27983,f27988,f27993,f27998,f28003,f28008,f28013,f28018,f28023,f28028,f28033,f28038,f28043,f28048,f28053,f28058,f28063,f28068,f28073,f28078,f28083,f28088,f28093,f28098,f28103,f28108,f28113,f28118,f28123,f28128,f28133,f28138,f28143,f28148,f28153,f28158,f28163,f28164,f28165,f28166,f28167,f28168,f28173,f28178,f28183,f28188,f28193,f28198,f28203,f28208,f28209,f28214,f28219,f28224,f28229,f28230,f28235,f28240,f28245,f28250,f28251,f28256,f28257,f28258,f28259,f28260,f28261,f28266,f28271,f28276,f28277,f28282,f28287,f28292,f28297,f28302,f28307,f28312,f28317,f28318,f28323,f28328,f28333,f28338,f28343,f28348,f28353,f28358,f28359,f28364,f28369,f28374,f28379,f28384,f28385,f28386,f28387,f28388,f28389,f28390,f28391,f28392,f28393,f28394,f28395,f28396,f28397,f28398,f28399,f28400,f28401,f28402,f28403,f28404,f28405,f28406,f28407,f28408,f28409,f28410,f28411,f28412,f28413,f28414,f28415,f28416,f28417,f28418,f28419,f28420,f28421,f28426,f28431,f28436,f28437,f28438,f28439,f28440,f28441,f28442,f28443,f28444,f28445,f28446,f28447,f28448,f28449,f28450,f28451,f28452,f28453,f28454,f28459,f28464,f28469,f28474,f28475,f28480,f28485,f28490,f28491,f28492,f28502,f28549,f28552,f28555,f28558,f28565,f28570,f28575,f28580,f28585,f28591,f28596,f28601,f28606,f28615,f28625,f28630,f28635,f28636,f28646,f28693,f28696,f28699,f28702,f28709,f28714,f28715,f28716,f28721,f28731,f28738,f28745,f28792,f28795,f28798,f28801,f28808,f28813,f28819,f28824,f28825,f28830,f28835,f28840,f28841,f28846,f28851,f28856,f28861,f28866,f28871,f28876,f28881,f28886,f28891,f28896,f28901,f28906,f28911,f28916,f28929,f28939,f28944,f28949,f28954,f28955,f28960,f28965,f28970,f28975,f28987,f28997,f29002,f29007,f29012,f29024,f29034,f29052,f29057,f29062,f29076,f29078,f29079,f29080,f29090,f29092,f29093,f29094,f29104,f29106,f29107,f29108,f29118,f29120,f29121,f29122,f29130,f29136,f29137,f29138,f29139,f29147,f29153,f29167,f29168,f29169,f29179,f29181,f29182,f29183,f29193,f29195,f29196,f29197,f29207,f29209,f29210,f29211,f29221,f29227,f29232,f29237,f29238,f29243,f29248,f29253,f29258,f29259,f29264,f29269,f29274,f29279,f29280,f29285,f29286,f29287,f29288,f29289,f29290,f29291,f29292,f29293,f29294,f29295,f29296,f29297,f29298,f29299,f29300,f29301,f29302,f29303,f29304,f29305,f29306,f29307,f29308,f29309,f29310,f29311,f29312,f29313,f29314,f29315,f29316,f29317,f29318,f29319,f29320,f29321,f29322,f29323,f29324,f29325,f29326,f29327,f29328,f29329,f29330,f29331,f29336,f29341,f29346,f29351,f29356,f29361,f29366,f29371,f29376,f29381,f29386,f29391,f29392,f29402,f29407,f29412,f29417,f29422,f29432,f29437,f29442,f29447,f29448,f29454,f29460,f29465,f29470,f29475,f29480,f29482,f29483,f29484,f29485,f29487,f29488,f29489,f29490,f29492,f29493,f29494,f29495,f29497,f29498,f29499,f29500,f29502,f29503,f29504,f29505,f29507,f29508,f29509,f29510,f29512,f29513,f29514,f29515,f29521,f29526,f29531,f29532,f29537,f29538,f29539,f29540,f29541,f29542,f29543,f29544,f29545,f29546,f29547,f29548,f29549,f29550,f29551,f29552,f29553,f29554,f29555,f29556,f29557,f29558,f29559,f29560,f29561,f29562,f29563,f29564,f29565,f29566,f29567,f29568,f29569,f29570,f29571,f29572,f29577,f29582,f29587,f29588,f29593,f29594,f29595,f29600,f29601,f29602,f29603,f29608,f29613,f29618,f29623,f29628,f29641,f29651,f29656,f29661,f29670,f29679,f29680,f29681,f29682,f29688,f29695,f29700,f29705,f29706,f29711,f29712,f29713,f29714,f29723,f29724,f29725,f29726,f29727,f29728,f29729,f29730,f29731,f29732,f29733,f29734,f29739,f29744,f29749,f29754,f29759,f29764,f29770,f29777,f29784,f29831,f29834,f29837,f29840,f29847,f29852,f29857,f29863,f29868,f29869,f29874,f29879,f29880,f29881,f29882,f29883,f29891,f30307,f30312,f30313,f30323,f30329,f30330,f30331,f30336,f30337,f30338,f30343,f30344,f30349,f30350,f30351,f30356,f30361,f30366,f30367,f30368,f30369,f30370,f30371,f30376,f30377,f30383,f30385,f30390,f30391,f30396,f30403,f30405,f30407,f30438,f30501,f30505,f30507,f30512,f30517,f30522,f30527,f30532,f30537,f30538,f30544,f30545,f30546,f30547,f30553,f30554,f30555,f30556,f30558,f30559,f30560,f30561,f30567,f30568,f30569,f30574,f30579,f30584,f30589,f30592,f30597,f30602,f30607,f30612,f30615,f30620,f30625,f30627,f30658,f30685,f30690,f30691,f30977,f30982,f30988,f30989,f30991,f30994,f30996,f31085,f31099,f31104,f31106,f31107,f31112,f31121,f31142,f31145,f31150,f31152,f31154,f31155,f31156,f31157,f31174,f31181,f31188,f31193,f31198,f31203,f31624,f31629,f31630,f31641,f31646,f31647,f31648,f31653,f31654,f31655,f31660,f31661,f31666,f31667,f31668,f31673,f31678,f31679,f31680,f31681,f31682,f31687,f31688,f31694,f31696,f31701,f31702,f31707,f31714,f31716,f31718,f31749,f31812,f31816,f31818,f31823,f31828,f31833,f31838,f31843,f31848,f31854,f31855,f31856,f31857,f31863,f31864,f31865,f31866,f31868,f31869,f31870,f31871,f31877,f31878,f31879,f31880,f31885,f31890,f31895,f31900,f31903,f31908,f31913,f31918,f31923,f31926,f31931,f31936,f31938,f31969,f31996,f32001,f32002,f32079,f32085,f32091,f32093,f32095,f32097,f32102,f32103,f32104,f32105,f32110,f32115,f32120,f32125,f32131,f32136,f32141,f32146,f32151,f32156,f32157,f32158,f32159,f32160,f32161,f32241,f32249,f32254,f32255,f32257,f32258,f32260,f32262,f32268,f32273,f32274,f32279,f32284,f32289,f32294,f32299,f32305,f32310,f32315,f32320,f32325,f32326,f32327,f32328,f32329,f32330])).

fof(f32330,plain,
    ( spl206_221
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32165,f8789,f8752,f24150])).

fof(f24150,plain,
    ( spl206_221
  <=> v1_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_221])])).

fof(f8752,plain,
    ( spl206_105
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_105])])).

fof(f8789,plain,
    ( spl206_112
  <=> v4_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_112])])).

fof(f32165,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8791,f4305])).

fof(f4305,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2189])).

fof(f2189,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2188])).

fof(f2188,plain,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) )
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f919])).

fof(f919,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X2)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v4_relat_1(k5_relat_1(X1,X2),X0)
        & v1_relat_1(k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc26_relat_1)).

fof(f8791,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl206_112 ),
    inference(avatar_component_clause,[],[f8789])).

fof(f8754,plain,
    ( v1_relat_1(sK3)
    | ~ spl206_105 ),
    inference(avatar_component_clause,[],[f8752])).

fof(f4298,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1114])).

fof(f1114,axiom,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_ordinal1)).

fof(f32329,plain,
    ( spl206_398
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32173,f8789,f8752,f28471])).

fof(f28471,plain,
    ( spl206_398
  <=> v1_relat_1(k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_398])])).

fof(f32173,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8791,f4305])).

fof(f32328,plain,
    ( spl206_401
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32180,f8789,f8752,f28487])).

fof(f28487,plain,
    ( spl206_401
  <=> v1_relat_1(k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_401])])).

fof(f32180,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK89))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8791,f4305])).

fof(f3462,plain,(
    v1_relat_1(sK89) ),
    inference(cnf_transformation,[],[f2441])).

fof(f2441,plain,
    ( v1_funct_1(sK89)
    & v1_relat_1(sK89) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK89])],[f930,f2440])).

fof(f2440,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK89)
      & v1_relat_1(sK89) ) ),
    introduced(choice_axiom,[])).

fof(f930,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_funct_1)).

fof(f32327,plain,
    ( spl206_400
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32181,f8789,f8752,f28482])).

fof(f28482,plain,
    ( spl206_400
  <=> v1_relat_1(k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_400])])).

fof(f32181,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK128))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8791,f4305])).

fof(f3572,plain,(
    v1_relat_1(sK128) ),
    inference(cnf_transformation,[],[f2522])).

fof(f2522,plain,
    ( v1_relat_1(sK128)
    & ~ v1_xboole_0(sK128) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK128])],[f702,f2521])).

fof(f2521,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK128)
      & ~ v1_xboole_0(sK128) ) ),
    introduced(choice_axiom,[])).

fof(f702,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

fof(f32326,plain,
    ( spl206_399
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32182,f8789,f8752,f28477])).

fof(f28477,plain,
    ( spl206_399
  <=> v1_relat_1(k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_399])])).

fof(f32182,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK162))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8791,f4305])).

fof(f3900,plain,(
    v1_relat_1(sK162) ),
    inference(cnf_transformation,[],[f2624])).

fof(f2624,plain,
    ( v2_funct_1(sK162)
    & v1_funct_1(sK162)
    & v1_relat_1(sK162) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK162])],[f931,f2623])).

fof(f2623,plain,
    ( ? [X0] :
        ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v2_funct_1(sK162)
      & v1_funct_1(sK162)
      & v1_relat_1(sK162) ) ),
    introduced(choice_axiom,[])).

fof(f931,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_funct_1)).

fof(f32325,plain,
    ( spl206_659
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32187,f8789,f8752,f32322])).

fof(f32322,plain,
    ( spl206_659
  <=> v4_relat_1(k5_relat_1(sK3,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_659])])).

fof(f32187,plain,
    ( v4_relat_1(k5_relat_1(sK3,k1_xboole_0),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8791,f4306])).

fof(f4306,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k5_relat_1(X1,X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2189])).

fof(f32320,plain,
    ( spl206_658
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32195,f8789,f8752,f32317])).

fof(f32317,plain,
    ( spl206_658
  <=> v4_relat_1(k5_relat_1(sK3,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_658])])).

fof(f32195,plain,
    ( v4_relat_1(k5_relat_1(sK3,sK3),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8791,f4306])).

fof(f32315,plain,
    ( spl206_657
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32202,f8789,f8752,f32312])).

fof(f32312,plain,
    ( spl206_657
  <=> v4_relat_1(k5_relat_1(sK3,sK89),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_657])])).

fof(f32202,plain,
    ( v4_relat_1(k5_relat_1(sK3,sK89),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8791,f4306])).

fof(f32310,plain,
    ( spl206_656
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32203,f8789,f8752,f32307])).

fof(f32307,plain,
    ( spl206_656
  <=> v4_relat_1(k5_relat_1(sK3,sK128),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_656])])).

fof(f32203,plain,
    ( v4_relat_1(k5_relat_1(sK3,sK128),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8791,f4306])).

fof(f32305,plain,
    ( spl206_655
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32204,f8789,f8752,f32302])).

fof(f32302,plain,
    ( spl206_655
  <=> v4_relat_1(k5_relat_1(sK3,sK162),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_655])])).

fof(f32204,plain,
    ( v4_relat_1(k5_relat_1(sK3,sK162),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8791,f4306])).

fof(f32299,plain,
    ( spl206_654
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32211,f8789,f8752,f32296])).

fof(f32296,plain,
    ( spl206_654
  <=> v4_relat_1(sK19(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_654])])).

fof(f32211,plain,
    ( v4_relat_1(sK19(sK3),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f2869,f8791,f4308])).

fof(f4308,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2193])).

fof(f2193,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2192])).

fof(f2192,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f642])).

fof(f642,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_relat_1)).

fof(f2869,plain,(
    ! [X0] : m1_subset_1(sK19(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2250])).

fof(f2250,plain,(
    ! [X0] :
      ( v1_xboole_0(sK19(X0))
      & m1_subset_1(sK19(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f490,f2249])).

fof(f2249,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK19(X0))
        & m1_subset_1(sK19(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f490,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc2_subset_1)).

fof(f32294,plain,
    ( spl206_653
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32212,f8789,f8752,f32291])).

fof(f32291,plain,
    ( spl206_653
  <=> v4_relat_1(sK20(k1_zfmisc_1(sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_653])])).

fof(f32212,plain,
    ( v4_relat_1(sK20(k1_zfmisc_1(sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f2871,f8791,f4308])).

fof(f2871,plain,(
    ! [X0] : m1_subset_1(sK20(X0),X0) ),
    inference(cnf_transformation,[],[f2252])).

fof(f2252,plain,(
    ! [X0] : m1_subset_1(sK20(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f474,f2251])).

fof(f2251,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK20(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f474,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f32289,plain,
    ( spl206_652
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32213,f8789,f8752,f32286])).

fof(f32286,plain,
    ( spl206_652
  <=> sK3 = k7_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_652])])).

fof(f32213,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8791,f4309])).

fof(f4309,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2195])).

fof(f2195,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2194])).

fof(f2194,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f813])).

fof(f813,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f32284,plain,
    ( spl206_651
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32216,f8789,f8752,f32281])).

fof(f32281,plain,
    ( spl206_651
  <=> v4_relat_1(sK3,k1_zfmisc_1(k3_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_651])])).

fof(f32216,plain,
    ( v4_relat_1(sK3,k1_zfmisc_1(k3_tarski(sK1)))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f8791,f4310])).

fof(f4310,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2197])).

fof(f2197,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2196])).

fof(f2196,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f822])).

fof(f822,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v4_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t217_relat_1)).

fof(f4083,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f320])).

fof(f320,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f32279,plain,
    ( spl206_650
    | ~ spl206_2
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32218,f8789,f8752,f5107,f32276])).

fof(f32276,plain,
    ( spl206_650
  <=> v4_relat_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_650])])).

fof(f5107,plain,
    ( spl206_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_2])])).

fof(f32218,plain,
    ( v4_relat_1(sK3,sK2)
    | ~ spl206_2
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f8791,f4310])).

fof(f5109,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl206_2 ),
    inference(avatar_component_clause,[],[f5107])).

fof(f32274,plain,
    ( spl206_649
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32219,f8789,f8752,f32270])).

fof(f32270,plain,
    ( spl206_649
  <=> r1_tarski(sK3,k7_relat_1(sK3,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_649])])).

fof(f32219,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,sK1))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4882,f8791,f4311])).

fof(f4311,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2199])).

fof(f2199,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2198])).

fof(f2198,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ v4_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f815])).

fof(f815,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( ( v4_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( r1_tarski(X2,X1)
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t210_relat_1)).

fof(f4882,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2806])).

fof(f2806,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2226])).

fof(f2226,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2225])).

fof(f2225,plain,(
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

fof(f32273,plain,
    ( spl206_649
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32220,f8789,f8752,f32270])).

fof(f32220,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,sK1))
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4881,f8791,f4311])).

fof(f4881,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2807])).

fof(f2807,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2226])).

fof(f32268,plain,
    ( spl206_648
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32221,f8789,f8752,f32265])).

fof(f32265,plain,
    ( spl206_648
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_648])])).

fof(f32221,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f8791,f4312])).

fof(f4312,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2744])).

fof(f2744,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2200])).

fof(f2200,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f32262,plain,
    ( spl206_647
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32261,f8789,f8752,f32251])).

fof(f32251,plain,
    ( spl206_647
  <=> v4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_647])])).

fof(f32261,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(forward_demodulation,[],[f32223,f4635])).

fof(f4635,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k3_tarski(k2_tarski(X1,X0)) ),
    inference(definition_unfolding,[],[f3293,f3631,f3631])).

fof(f3631,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f442])).

fof(f442,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

fof(f3293,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f32223,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f4288,f8791,f4869])).

fof(f4869,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f4307,f3631])).

fof(f4307,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2191])).

fof(f2191,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2190])).

fof(f2190,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v4_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1218])).

fof(f1218,axiom,(
    ! [X0,X1,X2] :
      ( ( v4_relat_1(X2,X0)
        & v1_relat_1(X2)
        & v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => v4_relat_1(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relset_1)).

fof(f4288,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f701])).

fof(f701,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l222_relat_1)).

fof(f32260,plain,
    ( spl206_647
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32259,f8789,f8752,f32251])).

fof(f32259,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(forward_demodulation,[],[f32224,f4635])).

fof(f32224,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f4286,f8791,f4869])).

fof(f4286,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f810])).

fof(f810,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t206_relat_1)).

fof(f32258,plain,
    ( spl206_646
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32225,f8789,f8752,f32246])).

fof(f32246,plain,
    ( spl206_646
  <=> v4_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_646])])).

fof(f32225,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK1))),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3823,f8791,f4869])).

fof(f3823,plain,(
    ! [X0] : v4_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f917])).

fof(f917,axiom,(
    ! [X0] :
      ( v5_relat_1(k6_relat_1(X0),X0)
      & v4_relat_1(k6_relat_1(X0),X0)
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc24_relat_1)).

fof(f3831,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f668])).

fof(f668,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f32257,plain,
    ( spl206_645
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32228,f8789,f8752,f32238])).

fof(f32238,plain,
    ( spl206_645
  <=> v4_relat_1(k3_tarski(k2_tarski(sK3,sK205(sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_645])])).

fof(f32228,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,sK205(sK1))),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f8754,f4314,f4316,f8791,f4869])).

fof(f4316,plain,(
    ! [X0] : v4_relat_1(sK205(X0),X0) ),
    inference(cnf_transformation,[],[f2746])).

fof(f2746,plain,(
    ! [X0] :
      ( v1_funct_1(sK205(X0))
      & v4_relat_1(sK205(X0),X0)
      & v2_relat_1(sK205(X0))
      & v1_relat_1(sK205(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK205])],[f1152,f2745])).

fof(f2745,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_funct_1(X1)
          & v4_relat_1(X1,X0)
          & v2_relat_1(X1)
          & v1_relat_1(X1) )
     => ( v1_funct_1(sK205(X0))
        & v4_relat_1(sK205(X0),X0)
        & v2_relat_1(sK205(X0))
        & v1_relat_1(sK205(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1152,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_funct_1(X1)
      & v4_relat_1(X1,X0)
      & v2_relat_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc9_funct_1)).

fof(f4314,plain,(
    ! [X0] : v1_relat_1(sK205(X0)) ),
    inference(cnf_transformation,[],[f2746])).

fof(f32255,plain,
    ( spl206_647
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32230,f8789,f8752,f32251])).

fof(f32230,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4298,f4288,f8754,f8791,f4869])).

fof(f32254,plain,
    ( spl206_647
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32231,f8789,f8752,f32251])).

fof(f32231,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4298,f4286,f8754,f8791,f4869])).

fof(f32249,plain,
    ( spl206_646
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32244,f8789,f8752,f32246])).

fof(f32244,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK1))),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(forward_demodulation,[],[f32232,f4635])).

fof(f32232,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(k6_relat_1(sK1),sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f3831,f3823,f8754,f8791,f4869])).

fof(f32241,plain,
    ( spl206_645
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(avatar_split_clause,[],[f32236,f8789,f8752,f32238])).

fof(f32236,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK3,sK205(sK1))),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(forward_demodulation,[],[f32235,f4635])).

fof(f32235,plain,
    ( v4_relat_1(k3_tarski(k2_tarski(sK205(sK1),sK3)),sK1)
    | ~ spl206_105
    | ~ spl206_112 ),
    inference(unit_resulting_resolution,[],[f4314,f4316,f8754,f8791,f4869])).

fof(f32161,plain,
    ( spl206_218
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32005,f8784,f8752,f24133])).

fof(f24133,plain,
    ( spl206_218
  <=> v1_relat_1(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_218])])).

fof(f8784,plain,
    ( spl206_111
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_111])])).

fof(f32005,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8786,f4258])).

fof(f4258,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(k5_relat_1(X2,X1))
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2167])).

fof(f2167,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) )
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2166])).

fof(f2166,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) )
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f918])).

fof(f918,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_relat_1(X2)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v5_relat_1(k5_relat_1(X2,X1),X0)
        & v1_relat_1(k5_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc25_relat_1)).

fof(f8786,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl206_111 ),
    inference(avatar_component_clause,[],[f8784])).

fof(f32160,plain,
    ( spl206_398
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32013,f8784,f8752,f28471])).

fof(f32013,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8786,f4258])).

fof(f32159,plain,
    ( spl206_397
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32020,f8784,f8752,f28466])).

fof(f28466,plain,
    ( spl206_397
  <=> v1_relat_1(k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_397])])).

fof(f32020,plain,
    ( v1_relat_1(k5_relat_1(sK89,sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8786,f4258])).

fof(f32158,plain,
    ( spl206_396
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32021,f8784,f8752,f28461])).

fof(f28461,plain,
    ( spl206_396
  <=> v1_relat_1(k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_396])])).

fof(f32021,plain,
    ( v1_relat_1(k5_relat_1(sK128,sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8786,f4258])).

fof(f32157,plain,
    ( spl206_395
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32022,f8784,f8752,f28456])).

fof(f28456,plain,
    ( spl206_395
  <=> v1_relat_1(k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_395])])).

fof(f32022,plain,
    ( v1_relat_1(k5_relat_1(sK162,sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8786,f4258])).

fof(f32156,plain,
    ( spl206_644
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32027,f8784,f8752,f32153])).

fof(f32153,plain,
    ( spl206_644
  <=> v5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_644])])).

fof(f32027,plain,
    ( v5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8786,f4259])).

fof(f4259,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k5_relat_1(X2,X1),X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2167])).

fof(f32151,plain,
    ( spl206_643
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32035,f8784,f8752,f32148])).

fof(f32148,plain,
    ( spl206_643
  <=> v5_relat_1(k5_relat_1(sK3,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_643])])).

fof(f32035,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8786,f4259])).

fof(f32146,plain,
    ( spl206_642
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32042,f8784,f8752,f32143])).

fof(f32143,plain,
    ( spl206_642
  <=> v5_relat_1(k5_relat_1(sK89,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_642])])).

fof(f32042,plain,
    ( v5_relat_1(k5_relat_1(sK89,sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8786,f4259])).

fof(f32141,plain,
    ( spl206_641
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32043,f8784,f8752,f32138])).

fof(f32138,plain,
    ( spl206_641
  <=> v5_relat_1(k5_relat_1(sK128,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_641])])).

fof(f32043,plain,
    ( v5_relat_1(k5_relat_1(sK128,sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8786,f4259])).

fof(f32136,plain,
    ( spl206_640
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32044,f8784,f8752,f32133])).

fof(f32133,plain,
    ( spl206_640
  <=> v5_relat_1(k5_relat_1(sK162,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_640])])).

fof(f32044,plain,
    ( v5_relat_1(k5_relat_1(sK162,sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8786,f4259])).

fof(f32131,plain,
    ( ~ spl206_639
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32049,f8784,f8752,f32128])).

fof(f32128,plain,
    ( spl206_639
  <=> r2_hidden(sK177(sK0),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_639])])).

fof(f32049,plain,
    ( ~ r2_hidden(sK177(sK0),k2_relat_1(sK3))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f4021,f8786,f4270])).

fof(f4270,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2172])).

fof(f2172,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2171])).

fof(f2171,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f806])).

fof(f806,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t202_relat_1)).

fof(f4021,plain,(
    ! [X0] : ~ r2_hidden(sK177(X0),X0) ),
    inference(cnf_transformation,[],[f2659])).

fof(f2659,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK177(X0),X0)
      & v3_ordinal1(sK177(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK177])],[f2073,f2658])).

fof(f2658,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(sK177(X0),X0)
        & v3_ordinal1(sK177(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2073,plain,(
    ! [X0] :
    ? [X1] :
      ( ~ r2_hidden(X1,X0)
      & v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f1109])).

fof(f1109,axiom,(
    ! [X0] :
      ~ ! [X1] :
          ( v3_ordinal1(X1)
         => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_ordinal1)).

fof(f32125,plain,
    ( spl206_638
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32052,f8784,f8752,f32122])).

fof(f32122,plain,
    ( spl206_638
  <=> v5_relat_1(sK19(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_638])])).

fof(f32052,plain,
    ( v5_relat_1(sK19(sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f2869,f8786,f4271])).

fof(f4271,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2174])).

fof(f2174,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2173])).

fof(f2173,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f643])).

fof(f643,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc6_relat_1)).

fof(f32120,plain,
    ( spl206_637
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32053,f8784,f8752,f32117])).

fof(f32117,plain,
    ( spl206_637
  <=> v5_relat_1(sK20(k1_zfmisc_1(sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_637])])).

fof(f32053,plain,
    ( v5_relat_1(sK20(k1_zfmisc_1(sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f2871,f8786,f4271])).

fof(f32115,plain,
    ( spl206_636
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32056,f8784,f8752,f32112])).

fof(f32112,plain,
    ( spl206_636
  <=> v5_relat_1(sK3,k1_zfmisc_1(k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_636])])).

fof(f32056,plain,
    ( v5_relat_1(sK3,k1_zfmisc_1(k3_tarski(sK0)))
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f8786,f4279])).

fof(f4279,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2180])).

fof(f2180,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2179])).

fof(f2179,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f823])).

fof(f823,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t218_relat_1)).

fof(f32110,plain,
    ( spl206_635
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32058,f8784,f8752,f32107])).

fof(f32107,plain,
    ( spl206_635
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_635])])).

fof(f32058,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f8786,f4284])).

fof(f4284,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2741])).

fof(f2741,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f2183])).

fof(f2183,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f652])).

fof(f652,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f32105,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32059,f8784,f8752,f32088])).

fof(f32088,plain,
    ( spl206_634
  <=> v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_634])])).

fof(f32059,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4298,f4299,f8754,f8786,f4868])).

fof(f4868,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f4260,f3631])).

fof(f4260,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2169])).

fof(f2169,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2168])).

fof(f2168,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(k2_xboole_0(X1,X2),X0)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1219])).

fof(f1219,axiom,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X0)
        & v1_relat_1(X2)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => v5_relat_1(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_relset_1)).

fof(f4299,plain,(
    ! [X0] : v5_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1114])).

fof(f32104,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32060,f8784,f8752,f32088])).

fof(f32060,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4298,f4289,f8754,f8786,f4868])).

fof(f4289,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f701])).

fof(f32103,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32061,f8784,f8752,f32088])).

fof(f32061,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4298,f4287,f8754,f8786,f4868])).

fof(f4287,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f810])).

fof(f32102,plain,
    ( spl206_633
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32101,f8784,f8752,f32082])).

fof(f32082,plain,
    ( spl206_633
  <=> v5_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_633])])).

fof(f32101,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK0))),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(forward_demodulation,[],[f32062,f4635])).

fof(f32062,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k6_relat_1(sK0),sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f3831,f3824,f8754,f8786,f4868])).

fof(f3824,plain,(
    ! [X0] : v5_relat_1(k6_relat_1(X0),X0) ),
    inference(cnf_transformation,[],[f917])).

fof(f32097,plain,
    ( spl206_632
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32096,f8784,f8752,f32076])).

fof(f32076,plain,
    ( spl206_632
  <=> v5_relat_1(k3_tarski(k2_tarski(sK3,sK204(sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_632])])).

fof(f32096,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,sK204(sK0))),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(forward_demodulation,[],[f32066,f4635])).

fof(f32066,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK204(sK0),sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f4290,f4291,f8754,f8786,f4868])).

fof(f4291,plain,(
    ! [X0] : v5_relat_1(sK204(X0),X0) ),
    inference(cnf_transformation,[],[f2743])).

fof(f2743,plain,(
    ! [X0] :
      ( v5_ordinal1(sK204(X0))
      & v1_funct_1(sK204(X0))
      & v5_relat_1(sK204(X0),X0)
      & v1_relat_1(sK204(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK204])],[f1082,f2742])).

fof(f2742,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v5_ordinal1(sK204(X0))
        & v1_funct_1(sK204(X0))
        & v5_relat_1(sK204(X0),X0)
        & v1_relat_1(sK204(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1082,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f4290,plain,(
    ! [X0] : v1_relat_1(sK204(X0)) ),
    inference(cnf_transformation,[],[f2743])).

fof(f32095,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32094,f8784,f8752,f32088])).

fof(f32094,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(forward_demodulation,[],[f32067,f4635])).

fof(f32067,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f4299,f8786,f4868])).

fof(f32093,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32092,f8784,f8752,f32088])).

fof(f32092,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(forward_demodulation,[],[f32068,f4635])).

fof(f32068,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f4289,f8786,f4868])).

fof(f32091,plain,
    ( spl206_634
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32086,f8784,f8752,f32088])).

fof(f32086,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(forward_demodulation,[],[f32069,f4635])).

fof(f32069,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f4287,f8786,f4868])).

fof(f32085,plain,
    ( spl206_633
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32070,f8784,f8752,f32082])).

fof(f32070,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,k6_relat_1(sK0))),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3824,f8786,f4868])).

fof(f32079,plain,
    ( spl206_632
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(avatar_split_clause,[],[f32074,f8784,f8752,f32076])).

fof(f32074,plain,
    ( v5_relat_1(k3_tarski(k2_tarski(sK3,sK204(sK0))),sK0)
    | ~ spl206_105
    | ~ spl206_111 ),
    inference(unit_resulting_resolution,[],[f8754,f4290,f4291,f8786,f4868])).

fof(f32002,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31213,f8762,f31711])).

fof(f31711,plain,
    ( spl206_609
  <=> r2_hidden(sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_609])])).

fof(f8762,plain,
    ( spl206_107
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_107])])).

fof(f31213,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f2830,f8764,f2803])).

fof(f2803,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2224])).

fof(f2224,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK8(X0,X1),X1)
          & r2_hidden(sK8(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f2222,f2223])).

fof(f2223,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK8(X0,X1),X1)
        & r2_hidden(sK8(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2222,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f2221])).

fof(f2221,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1300])).

fof(f1300,plain,(
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

fof(f8764,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl206_107 ),
    inference(avatar_component_clause,[],[f8762])).

fof(f2830,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32001,plain,
    ( ~ spl206_631
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31216,f8762,f31998])).

fof(f31998,plain,
    ( spl206_631
  <=> r2_hidden(sK1,k2_relat_1(sK6(sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_631])])).

fof(f31216,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4871,f8764,f2803])).

fof(f4871,plain,(
    ! [X0] : r1_tarski(k2_relat_1(sK6(X0,k1_xboole_0)),X0) ),
    inference(equality_resolution,[],[f2785])).

fof(f2785,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(sK6(X0,X1)),X0)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2209])).

fof(f2209,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k2_relat_1(sK6(X0,X1)),X0)
        & k1_relat_1(sK6(X0,X1)) = X1
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f1298,f2208])).

fof(f2208,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( r1_tarski(k2_relat_1(sK6(X0,X1)),X0)
        & k1_relat_1(sK6(X0,X1)) = X1
        & v1_funct_1(sK6(X0,X1))
        & v1_relat_1(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1298,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f1297])).

fof(f1297,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( r1_tarski(k2_relat_1(X2),X0)
          & k1_relat_1(X2) = X1
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
      | ( k1_xboole_0 != X1
        & k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f1001])).

fof(f1001,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ( ( v1_funct_1(X2)
              & v1_relat_1(X2) )
           => ~ ( r1_tarski(k2_relat_1(X2),X0)
                & k1_relat_1(X2) = X1 ) )
        & ~ ( k1_xboole_0 != X1
            & k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_funct_1)).

fof(f31996,plain,
    ( ~ spl206_607
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31219,f8762,f31698])).

fof(f31698,plain,
    ( spl206_607
  <=> r1_tarski(k2_tarski(sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_607])])).

fof(f31219,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4904,f8764,f2803])).

fof(f4904,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f4903])).

fof(f4903,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f4448])).

fof(f4448,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f3084,f3202])).

fof(f3202,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f254])).

fof(f254,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f3084,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2326])).

fof(f2326,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK49(X0,X1) != X0
            | ~ r2_hidden(sK49(X0,X1),X1) )
          & ( sK49(X0,X1) = X0
            | r2_hidden(sK49(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK49])],[f2324,f2325])).

fof(f2325,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK49(X0,X1) != X0
          | ~ r2_hidden(sK49(X0,X1),X1) )
        & ( sK49(X0,X1) = X0
          | r2_hidden(sK49(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2324,plain,(
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
    inference(rectify,[],[f2323])).

fof(f2323,plain,(
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

fof(f31969,plain,
    ( ~ spl206_630
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31255,f8762,f31966])).

fof(f31966,plain,
    ( spl206_630
  <=> m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_630])])).

fof(f31255,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4904,f8764,f2852])).

fof(f2852,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1340])).

fof(f1340,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f488])).

fof(f488,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f31938,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31291,f8762,f31711])).

fof(f31291,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f2878,f8764,f2852])).

fof(f2878,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f31936,plain,
    ( ~ spl206_629
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31293,f8762,f31933])).

fof(f31933,plain,
    ( spl206_629
  <=> r2_hidden(sK1,sK19(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_629])])).

fof(f31293,plain,
    ( ~ r2_hidden(sK1,sK19(sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f2869,f8764,f2852])).

fof(f31931,plain,
    ( ~ spl206_628
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31294,f8762,f31928])).

fof(f31928,plain,
    ( spl206_628
  <=> r2_hidden(sK1,sK20(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_628])])).

fof(f31294,plain,
    ( ~ r2_hidden(sK1,sK20(k1_zfmisc_1(sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f2871,f8764,f2852])).

fof(f31926,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31925,f8762,f31711])).

fof(f31925,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31924,f3391])).

fof(f3391,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f856,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f31924,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k1_xboole_0))
    | spl206_107 ),
    inference(forward_demodulation,[],[f31299,f3060])).

fof(f3060,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f716])).

fof(f716,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f31299,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(k1_xboole_0,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f8764,f2991])).

fof(f2991,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2291])).

fof(f2291,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2290])).

fof(f2290,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1415])).

fof(f1415,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f875])).

fof(f875,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f31923,plain,
    ( ~ spl206_627
    | ~ spl206_105
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31307,f8762,f8752,f31920])).

fof(f31920,plain,
    ( spl206_627
  <=> r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_627])])).

fof(f31307,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK3,sK3)))
    | ~ spl206_105
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8754,f8764,f2991])).

fof(f31918,plain,
    ( ~ spl206_626
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31314,f8762,f31915])).

fof(f31915,plain,
    ( spl206_626
  <=> r2_hidden(sK1,k1_relat_1(k7_relat_1(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_626])])).

fof(f31314,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK89,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3462,f8764,f2991])).

fof(f31913,plain,
    ( ~ spl206_625
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31315,f8762,f31910])).

fof(f31910,plain,
    ( spl206_625
  <=> r2_hidden(sK1,k1_relat_1(k7_relat_1(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_625])])).

fof(f31315,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK128,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3572,f8764,f2991])).

fof(f31908,plain,
    ( ~ spl206_624
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31316,f8762,f31905])).

fof(f31905,plain,
    ( spl206_624
  <=> r2_hidden(sK1,k1_relat_1(k7_relat_1(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_624])])).

fof(f31316,plain,
    ( ~ r2_hidden(sK1,k1_relat_1(k7_relat_1(sK162,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3900,f8764,f2991])).

fof(f31903,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31902,f8762,f31711])).

fof(f31902,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31901,f3392])).

fof(f3392,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f856])).

fof(f31901,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k1_xboole_0))
    | spl206_107 ),
    inference(forward_demodulation,[],[f31321,f3803])).

fof(f3803,plain,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f741])).

fof(f741,axiom,(
    ! [X0] : k1_xboole_0 = k8_relat_1(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

fof(f31321,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,k1_xboole_0)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f8764,f3304])).

fof(f3304,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2366])).

fof(f2366,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2365])).

fof(f2365,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
          | ~ r2_hidden(X0,k2_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k2_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1629])).

fof(f1629,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f718])).

fof(f718,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k2_relat_1(k8_relat_1(X1,X2)))
      <=> ( r2_hidden(X0,k2_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_relat_1)).

fof(f31900,plain,
    ( ~ spl206_623
    | ~ spl206_105
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31329,f8762,f8752,f31897])).

fof(f31897,plain,
    ( spl206_623
  <=> r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_623])])).

fof(f31329,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK3)))
    | ~ spl206_105
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8754,f8764,f3304])).

fof(f31895,plain,
    ( ~ spl206_622
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31336,f8762,f31892])).

fof(f31892,plain,
    ( spl206_622
  <=> r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_622])])).

fof(f31336,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK89)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3462,f8764,f3304])).

fof(f31890,plain,
    ( ~ spl206_621
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31337,f8762,f31887])).

fof(f31887,plain,
    ( spl206_621
  <=> r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_621])])).

fof(f31337,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK128)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3572,f8764,f3304])).

fof(f31885,plain,
    ( ~ spl206_620
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31338,f8762,f31882])).

fof(f31882,plain,
    ( spl206_620
  <=> r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_620])])).

fof(f31338,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k8_relat_1(sK3,sK162)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3900,f8764,f3304])).

fof(f31880,plain,
    ( spl206_602
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31389,f8762,f31663])).

fof(f31663,plain,
    ( spl206_602
  <=> sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_602])])).

fof(f31389,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3609])).

fof(f3609,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1810])).

fof(f1810,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f361])).

fof(f361,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f31879,plain,
    ( spl206_619
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31390,f8762,f31874])).

fof(f31874,plain,
    ( spl206_619
  <=> sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK177(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_619])])).

fof(f31390,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK177(sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3609])).

fof(f31878,plain,
    ( spl206_602
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31391,f8762,f31663])).

fof(f31391,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3609])).

fof(f31877,plain,
    ( spl206_619
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31872,f8762,f31874])).

fof(f31872,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK177(sK3)))
    | spl206_107 ),
    inference(forward_demodulation,[],[f31392,f3634])).

fof(f3634,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f173])).

fof(f173,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f31392,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK177(sK3),sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3609])).

fof(f31871,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31393,f8762,f31650])).

fof(f31650,plain,
    ( spl206_600
  <=> r1_xboole_0(k2_tarski(sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_600])])).

fof(f31393,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3610])).

fof(f3610,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1811])).

fof(f1811,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f415])).

fof(f415,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f31870,plain,
    ( spl206_618
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31394,f8762,f31860])).

fof(f31860,plain,
    ( spl206_618
  <=> r1_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_618])])).

fof(f31394,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3610])).

fof(f31869,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31395,f8762,f31650])).

fof(f31395,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3610])).

fof(f31868,plain,
    ( spl206_618
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31867,f8762,f31860])).

fof(f31867,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31396,f3634])).

fof(f31396,plain,
    ( r1_xboole_0(k2_tarski(sK177(sK3),sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3610])).

fof(f31866,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31397,f8762,f31650])).

fof(f31397,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3611])).

fof(f3611,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1812])).

fof(f1812,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f301])).

fof(f301,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l168_zfmisc_1)).

fof(f31865,plain,
    ( spl206_618
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31398,f8762,f31860])).

fof(f31398,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3611])).

fof(f31864,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31399,f8762,f31650])).

fof(f31399,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3611])).

fof(f31863,plain,
    ( spl206_618
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31858,f8762,f31860])).

fof(f31858,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31400,f3634])).

fof(f31400,plain,
    ( r1_xboole_0(k2_tarski(sK177(sK3),sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3611])).

fof(f31857,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31401,f8762,f31626])).

fof(f31626,plain,
    ( spl206_597
  <=> k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_597])])).

fof(f31401,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3615])).

fof(f3615,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2534])).

fof(f2534,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f2533])).

fof(f2533,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f428])).

fof(f428,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f31856,plain,
    ( spl206_617
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31402,f8762,f31851])).

fof(f31851,plain,
    ( spl206_617
  <=> k2_tarski(sK1,sK177(sK3)) = k4_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_617])])).

fof(f31402,plain,
    ( k2_tarski(sK1,sK177(sK3)) = k4_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3615])).

fof(f31855,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31403,f8762,f31626])).

fof(f31403,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f3615])).

fof(f31854,plain,
    ( spl206_617
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31849,f8762,f31851])).

fof(f31849,plain,
    ( k2_tarski(sK1,sK177(sK3)) = k4_xboole_0(k2_tarski(sK1,sK177(sK3)),sK3)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31404,f3634])).

fof(f31404,plain,
    ( k2_tarski(sK177(sK3),sK1) = k4_xboole_0(k2_tarski(sK177(sK3),sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f3615])).

fof(f31848,plain,
    ( ~ spl206_616
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31407,f8762,f31845])).

fof(f31845,plain,
    ( spl206_616
  <=> r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_616])])).

fof(f31407,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(k1_xboole_0,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f8764,f3743])).

fof(f3743,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1862])).

fof(f1862,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1861])).

fof(f1861,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,X1)
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1163])).

fof(f1163,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k3_relat_1(k2_wellord1(X2,X1)))
       => ( r2_hidden(X0,X1)
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_wellord1)).

fof(f31843,plain,
    ( ~ spl206_615
    | ~ spl206_105
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31415,f8762,f8752,f31840])).

fof(f31840,plain,
    ( spl206_615
  <=> r2_hidden(sK1,k3_relat_1(k2_wellord1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_615])])).

fof(f31415,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK3,sK3)))
    | ~ spl206_105
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8754,f8764,f3743])).

fof(f31838,plain,
    ( ~ spl206_614
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31422,f8762,f31835])).

fof(f31835,plain,
    ( spl206_614
  <=> r2_hidden(sK1,k3_relat_1(k2_wellord1(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_614])])).

fof(f31422,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK89,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3462,f8764,f3743])).

fof(f31833,plain,
    ( ~ spl206_613
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31423,f8762,f31830])).

fof(f31830,plain,
    ( spl206_613
  <=> r2_hidden(sK1,k3_relat_1(k2_wellord1(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_613])])).

fof(f31423,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK128,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3572,f8764,f3743])).

fof(f31828,plain,
    ( ~ spl206_612
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31424,f8762,f31825])).

fof(f31825,plain,
    ( spl206_612
  <=> r2_hidden(sK1,k3_relat_1(k2_wellord1(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_612])])).

fof(f31424,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k2_wellord1(sK162,sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f3900,f8764,f3743])).

fof(f31823,plain,
    ( ~ spl206_611
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31429,f8762,f31820])).

fof(f31820,plain,
    ( spl206_611
  <=> r2_hidden(sK1,sK175(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_611])])).

fof(f31429,plain,
    ( ~ r2_hidden(sK1,sK175(sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4015])).

fof(f4015,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,sK175(X0)) ) ),
    inference(cnf_transformation,[],[f2654])).

fof(f2654,plain,(
    ! [X0,X2] :
      ( ( r2_hidden(X2,sK175(X0))
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,sK175(X0)) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK175])],[f2652,f2653])).

fof(f2653,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ( r2_hidden(X2,X1)
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,X1) ) )
     => ! [X2] :
          ( ( r2_hidden(X2,sK175(X0))
            | ~ v3_ordinal1(X2)
            | ~ r2_hidden(X2,X0) )
          & ( ( v3_ordinal1(X2)
              & r2_hidden(X2,X0) )
            | ~ r2_hidden(X2,sK175(X0)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2652,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(flattening,[],[f2651])).

fof(f2651,plain,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( ( r2_hidden(X2,X1)
        | ~ v3_ordinal1(X2)
        | ~ r2_hidden(X2,X0) )
      & ( ( v3_ordinal1(X2)
          & r2_hidden(X2,X0) )
        | ~ r2_hidden(X2,X1) ) ) ),
    inference(nnf_transformation,[],[f1087])).

fof(f1087,axiom,(
    ! [X0] :
    ? [X1] :
    ! [X2] :
      ( r2_hidden(X2,X1)
    <=> ( v3_ordinal1(X2)
        & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e3_53__ordinal1)).

fof(f31818,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31817,f8762,f31711])).

fof(f31817,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31430,f4061])).

fof(f4061,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f164])).

fof(f164,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f31430,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK3,sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f4035])).

fof(f4035,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f2667])).

fof(f2667,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f2084])).

fof(f2084,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f31816,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31815,f8762,f31711])).

fof(f31815,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31433,f4061])).

fof(f31433,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK3,sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f4035])).

fof(f31812,plain,
    ( spl206_610
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31811,f8762,f31746])).

fof(f31746,plain,
    ( spl206_610
  <=> r2_hidden(sK1,k5_xboole_0(sK3,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_610])])).

fof(f31811,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(forward_demodulation,[],[f31436,f4059])).

fof(f4059,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f31436,plain,
    ( r2_hidden(sK1,k5_xboole_0(k2_tarski(sK1,sK1),sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4904,f8764,f4037])).

fof(f4037,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2667])).

fof(f31749,plain,
    ( spl206_610
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31472,f8762,f31746])).

fof(f31472,plain,
    ( r2_hidden(sK1,k5_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4904,f8764,f4038])).

fof(f4038,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2667])).

fof(f31718,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31717,f8762,f31711])).

fof(f31717,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31508,f3392])).

fof(f31508,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k1_xboole_0))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f4299,f8764,f4270])).

fof(f31716,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31715,f8762,f31711])).

fof(f31715,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31509,f3392])).

fof(f31509,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k1_xboole_0))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f4289,f8764,f4270])).

fof(f31714,plain,
    ( ~ spl206_609
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31709,f8762,f31711])).

fof(f31709,plain,
    ( ~ r2_hidden(sK1,k1_xboole_0)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31510,f3392])).

fof(f31510,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(k1_xboole_0))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4298,f4287,f8764,f4270])).

fof(f31707,plain,
    ( ~ spl206_608
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31514,f8762,f31704])).

fof(f31704,plain,
    ( spl206_608
  <=> r2_hidden(sK1,k2_relat_1(sK204(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_608])])).

fof(f31514,plain,
    ( ~ r2_hidden(sK1,k2_relat_1(sK204(sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4290,f4291,f8764,f4270])).

fof(f31702,plain,
    ( ~ spl206_607
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31515,f8762,f31698])).

fof(f31515,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4349])).

fof(f4349,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f2787,f3202])).

fof(f2787,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2210])).

fof(f2210,plain,(
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

fof(f31701,plain,
    ( ~ spl206_607
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31516,f8762,f31698])).

fof(f31516,plain,
    ( ~ r1_tarski(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4351])).

fof(f4351,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f2789,f3202])).

fof(f2789,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2211])).

fof(f2211,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f302])).

fof(f302,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f31696,plain,
    ( ~ spl206_606
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31695,f8762,f31691])).

fof(f31691,plain,
    ( spl206_606
  <=> r1_tarski(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_606])])).

fof(f31695,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),sK3)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31517,f4635])).

fof(f31517,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK3)),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4358])).

fof(f4358,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1) ) ),
    inference(definition_unfolding,[],[f2809,f3631,f3202])).

fof(f2809,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f1301])).

fof(f1301,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f303])).

fof(f303,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l20_zfmisc_1)).

fof(f31694,plain,
    ( ~ spl206_606
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31689,f8762,f31691])).

fof(f31689,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),sK3)
    | spl206_107 ),
    inference(forward_demodulation,[],[f31518,f4635])).

fof(f31518,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK1,sK1),sK3)),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4359])).

fof(f4359,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(X0,X0),X1)),X1) ) ),
    inference(definition_unfolding,[],[f2810,f3631,f3202])).

fof(f2810,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f1302])).

fof(f1302,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f403])).

fof(f403,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f31688,plain,
    ( ~ spl206_605
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31521,f8762,f31684])).

fof(f31684,plain,
    ( spl206_605
  <=> k2_tarski(sK1,sK1) = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_605])])).

fof(f31521,plain,
    ( k2_tarski(sK1,sK1) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4450])).

fof(f4450,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_tarski(X1,X1) != k4_xboole_0(X0,k4_xboole_0(X0,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f3087,f3202,f3248,f3202])).

fof(f3248,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f110])).

fof(f110,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3087,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f1498])).

fof(f1498,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f307])).

fof(f307,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f31687,plain,
    ( ~ spl206_605
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31522,f8762,f31684])).

fof(f31522,plain,
    ( k2_tarski(sK1,sK1) != k4_xboole_0(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4451])).

fof(f4451,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_tarski(X1,X1) != k4_xboole_0(X0,k4_xboole_0(X0,k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f3088,f3202,f3248,f3202])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f1499])).

fof(f1499,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f409])).

fof(f409,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

fof(f31682,plain,
    ( spl206_604
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31524,f8762,f31675])).

fof(f31675,plain,
    ( spl206_604
  <=> r1_tarski(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_604])])).

fof(f31524,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4882,f8764,f4493])).

fof(f4493,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f3140,f3202])).

fof(f3140,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1525])).

fof(f1525,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1524])).

fof(f1524,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f398])).

fof(f398,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_zfmisc_1)).

fof(f31681,plain,
    ( spl206_604
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31525,f8762,f31675])).

fof(f31525,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4881,f8764,f4493])).

fof(f31680,plain,
    ( spl206_603
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31526,f8762,f31670])).

fof(f31670,plain,
    ( spl206_603
  <=> r1_tarski(sK3,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK3)),k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_603])])).

fof(f31526,plain,
    ( r1_tarski(sK3,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK3)),k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4083,f8764,f4493])).

fof(f31679,plain,
    ( spl206_604
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31528,f8762,f31675])).

fof(f31528,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4882,f8764,f4494])).

fof(f4494,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k2_tarski(X2,X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f3141,f3202])).

fof(f3141,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1527])).

fof(f1527,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1526])).

fof(f1526,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f308])).

fof(f308,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(f31678,plain,
    ( spl206_604
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31529,f8762,f31675])).

fof(f31529,plain,
    ( r1_tarski(sK3,k4_xboole_0(sK3,k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4881,f8764,f4494])).

fof(f31673,plain,
    ( spl206_603
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31530,f8762,f31670])).

fof(f31530,plain,
    ( r1_tarski(sK3,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK3)),k2_tarski(sK1,sK1)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4083,f8764,f4494])).

fof(f31668,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31532,f8762,f31626])).

fof(f31532,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4506])).

fof(f4506,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f3154,f3202,f3202])).

fof(f3154,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2346])).

fof(f2346,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f310])).

fof(f310,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f31667,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31533,f8762,f31626])).

fof(f31533,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4508])).

fof(f4508,plain,(
    ! [X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f3156,f3202,f3202])).

fof(f3156,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f2347])).

fof(f2347,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f423])).

fof(f423,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f31666,plain,
    ( spl206_602
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31534,f8762,f31663])).

fof(f31534,plain,
    ( sK3 = k4_xboole_0(sK3,k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4510])).

fof(f4510,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f3158,f3202])).

fof(f3158,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f2348])).

fof(f2348,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f421])).

fof(f421,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f31661,plain,
    ( ~ spl206_601
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31535,f8762,f31657])).

fof(f31657,plain,
    ( spl206_601
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK1,sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_601])])).

fof(f31535,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4513])).

fof(f4513,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f3159,f3202])).

fof(f3159,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2349])).

fof(f2349,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f424])).

fof(f424,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_zfmisc_1)).

fof(f31660,plain,
    ( ~ spl206_601
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31536,f8762,f31657])).

fof(f31536,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4515])).

fof(f4515,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k2_tarski(X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f3161,f3202])).

fof(f3161,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f2350])).

fof(f2350,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f311])).

fof(f311,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f31655,plain,
    ( spl206_599
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31537,f8762,f31643])).

fof(f31643,plain,
    ( spl206_599
  <=> sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_599])])).

fof(f31537,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4522])).

fof(f4522,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_tarski(k2_tarski(X1,k2_tarski(X0,X0))),k2_tarski(X0,X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f3169,f3631,f3202,f3202])).

fof(f3169,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1545])).

fof(f1545,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f358])).

fof(f358,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f31654,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31538,f8762,f31650])).

fof(f31538,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4523])).

fof(f4523,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f3170,f3202])).

fof(f3170,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1546])).

fof(f1546,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f306])).

fof(f306,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f31653,plain,
    ( spl206_600
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31539,f8762,f31650])).

fof(f31539,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4524])).

fof(f4524,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f3171,f3202])).

fof(f3171,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1547])).

fof(f1547,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f414])).

fof(f414,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_zfmisc_1)).

fof(f31648,plain,
    ( spl206_599
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31541,f8762,f31643])).

fof(f31541,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f4609])).

fof(f4609,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k3_tarski(k2_tarski(X2,k2_tarski(X0,X1))),k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f3267,f3631])).

fof(f3267,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1600])).

fof(f1600,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f362])).

fof(f362,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f31647,plain,
    ( spl206_598
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31542,f8762,f31638])).

fof(f31638,plain,
    ( spl206_598
  <=> sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK177(sK3)))),k2_tarski(sK1,sK177(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_598])])).

fof(f31542,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK177(sK3)))),k2_tarski(sK1,sK177(sK3)))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f4609])).

fof(f31646,plain,
    ( spl206_599
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31543,f8762,f31643])).

fof(f31543,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK1))),k2_tarski(sK1,sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f8764,f4609])).

fof(f31641,plain,
    ( spl206_598
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31636,f8762,f31638])).

fof(f31636,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK1,sK177(sK3)))),k2_tarski(sK1,sK177(sK3)))
    | spl206_107 ),
    inference(forward_demodulation,[],[f31544,f3634])).

fof(f31544,plain,
    ( sK3 = k4_xboole_0(k3_tarski(k2_tarski(sK3,k2_tarski(sK177(sK3),sK1))),k2_tarski(sK177(sK3),sK1))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4021,f8764,f4609])).

fof(f31630,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31554,f8762,f31626])).

fof(f31554,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4906])).

fof(f4906,plain,(
    ! [X2,X1] :
      ( k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f4469])).

fof(f4469,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f3113,f3202])).

fof(f3113,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2334])).

fof(f2334,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f2333])).

fof(f2333,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f427])).

fof(f427,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_zfmisc_1)).

fof(f31629,plain,
    ( spl206_597
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31555,f8762,f31626])).

fof(f31555,plain,
    ( k2_tarski(sK1,sK1) = k4_xboole_0(k2_tarski(sK1,sK1),sK3)
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f8764,f4907])).

fof(f4907,plain,(
    ! [X2,X1] :
      ( k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(equality_resolution,[],[f4473])).

fof(f4473,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f3117,f3202])).

fof(f3117,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | X0 != X1
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2336])).

fof(f2336,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f2335])).

fof(f2335,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f312])).

fof(f312,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f31624,plain,
    ( spl206_596
    | spl206_107 ),
    inference(avatar_split_clause,[],[f31557,f8762,f31621])).

fof(f31621,plain,
    ( spl206_596
  <=> r2_hidden(sK1,k4_xboole_0(k2_tarski(sK1,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_596])])).

fof(f31557,plain,
    ( r2_hidden(sK1,k4_xboole_0(k2_tarski(sK1,sK1),sK3))
    | spl206_107 ),
    inference(unit_resulting_resolution,[],[f4904,f8764,f4980])).

fof(f4980,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f3639])).

fof(f3639,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2546])).

fof(f2546,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK133(X0,X1,X2),X1)
            | ~ r2_hidden(sK133(X0,X1,X2),X0)
            | ~ r2_hidden(sK133(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK133(X0,X1,X2),X1)
              & r2_hidden(sK133(X0,X1,X2),X0) )
            | r2_hidden(sK133(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK133])],[f2544,f2545])).

fof(f2545,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK133(X0,X1,X2),X1)
          | ~ r2_hidden(sK133(X0,X1,X2),X0)
          | ~ r2_hidden(sK133(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK133(X0,X1,X2),X1)
            & r2_hidden(sK133(X0,X1,X2),X0) )
          | r2_hidden(sK133(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2544,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f2543])).

fof(f2543,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f2542])).

fof(f2542,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f31203,plain,
    ( spl206_595
    | ~ spl206_102
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f30702,f8752,f8733,f31200])).

fof(f31200,plain,
    ( spl206_595
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_595])])).

fof(f8733,plain,
    ( spl206_102
  <=> r1_xboole_0(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_102])])).

fof(f30702,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),sK3)
    | ~ spl206_102
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8735,f2997])).

fof(f2997,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1423])).

fof(f1423,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1422])).

fof(f1422,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f811])).

fof(f811,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f8735,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl206_102 ),
    inference(avatar_component_clause,[],[f8733])).

fof(f31198,plain,
    ( spl206_594
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30709,f8733,f31195])).

fof(f31195,plain,
    ( spl206_594
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK89,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_594])])).

fof(f30709,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK89,k1_xboole_0),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3462,f8735,f2997])).

fof(f31193,plain,
    ( spl206_593
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30710,f8733,f31190])).

fof(f31190,plain,
    ( spl206_593
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK128,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_593])])).

fof(f30710,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK128,k1_xboole_0),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3572,f8735,f2997])).

fof(f31188,plain,
    ( spl206_592
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30711,f8733,f31185])).

fof(f31185,plain,
    ( spl206_592
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK162,k1_xboole_0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_592])])).

fof(f30711,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK162,k1_xboole_0),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3900,f8735,f2997])).

fof(f31181,plain,
    ( spl206_589
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30736,f8733,f31118])).

fof(f31118,plain,
    ( spl206_589
  <=> r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_589])])).

fof(f30736,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4871,f4882,f8735,f3659])).

fof(f3659,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1830])).

fof(f1830,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1829])).

fof(f1829,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f130])).

fof(f130,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f31174,plain,
    ( spl206_589
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30744,f8733,f31118])).

fof(f30744,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4871,f4881,f8735,f3659])).

fof(f31157,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30771,f8733,f31139])).

fof(f31139,plain,
    ( spl206_590
  <=> r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_590])])).

fof(f30771,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4882,f4871,f8735,f3659])).

fof(f31156,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30772,f8733,f31139])).

fof(f30772,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4881,f4871,f8735,f3659])).

fof(f31155,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30773,f8733,f31139])).

fof(f30773,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f2830,f4871,f8735,f3659])).

fof(f31154,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f31153,f8733,f31139])).

fof(f31153,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30774,f3489])).

fof(f3489,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f30774,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4365,f4871,f8735,f3659])).

fof(f4365,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f2822,f3248])).

fof(f2822,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f31152,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f31151,f8733,f31139])).

fof(f31151,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30775,f3489])).

fof(f30775,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3657,f4871,f8735,f3659])).

fof(f3657,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f31150,plain,
    ( spl206_591
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30776,f8733,f31147])).

fof(f31147,plain,
    ( spl206_591
  <=> r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK6(sK3,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_591])])).

fof(f30776,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4871,f4871,f8735,f3659])).

fof(f31145,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f31144,f8733,f31139])).

fof(f31144,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f31143,f3391])).

fof(f31143,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30777,f4893])).

fof(f4893,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f2956])).

fof(f2956,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f2286])).

fof(f2286,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f2285])).

fof(f2285,plain,(
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

fof(f30777,plain,
    ( ! [X0] : r1_xboole_0(k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f2970,f4871,f8735,f3659])).

fof(f2970,plain,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    inference(cnf_transformation,[],[f796])).

fof(f796,axiom,(
    ! [X0,X1] : r1_tarski(k1_relat_1(k2_zfmisc_1(X0,X1)),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t193_relat_1)).

fof(f31142,plain,
    ( spl206_590
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f31137,f8733,f31139])).

fof(f31137,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f31136,f3392])).

fof(f31136,plain,
    ( r1_xboole_0(k2_relat_1(k1_xboole_0),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30778,f4892])).

fof(f4892,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f2957])).

fof(f2957,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2286])).

fof(f30778,plain,
    ( ! [X0] : r1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)),k2_relat_1(sK6(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f2971,f4871,f8735,f3659])).

fof(f2971,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f797])).

fof(f797,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f31121,plain,
    ( spl206_589
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30800,f8733,f31118])).

fof(f30800,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4871,f8735,f3665])).

fof(f3665,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1834])).

fof(f1834,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1833])).

fof(f1833,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f129])).

fof(f129,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f31112,plain,
    ( spl206_588
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30811,f8733,f31109])).

fof(f31109,plain,
    ( spl206_588
  <=> r1_xboole_0(k9_relat_1(sK162,k1_xboole_0),k9_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_588])])).

fof(f30811,plain,
    ( r1_xboole_0(k9_relat_1(sK162,k1_xboole_0),k9_relat_1(sK162,sK3))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f3902,f8735,f3666])).

fof(f3666,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1836])).

fof(f1836,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1835])).

fof(f1835,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ v2_funct_1(X2)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f954])).

fof(f954,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( v2_funct_1(X2)
          & r1_xboole_0(X0,X1) )
       => r1_xboole_0(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_funct_1)).

fof(f3902,plain,(
    v2_funct_1(sK162) ),
    inference(cnf_transformation,[],[f2624])).

fof(f3901,plain,(
    v1_funct_1(sK162) ),
    inference(cnf_transformation,[],[f2624])).

fof(f31107,plain,
    ( spl206_99
    | ~ spl206_3
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30814,f8733,f5112,f8717])).

fof(f8717,plain,
    ( spl206_99
  <=> r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_99])])).

fof(f5112,plain,
    ( spl206_3
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_3])])).

fof(f30814,plain,
    ( r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f5114,f2868,f8735,f3676])).

fof(f3676,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X3))
      | ~ r1_xboole_0(X3,X2)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1843])).

fof(f1843,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( r1_tarski(X1,k3_subset_1(X0,X3))
              | ~ r1_xboole_0(X3,X2)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f1842])).

fof(f1842,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ! [X3] :
              ( r1_tarski(X1,k3_subset_1(X0,X3))
              | ~ r1_xboole_0(X3,X2)
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f519])).

fof(f519,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(X0))
             => ( ( r1_xboole_0(X3,X2)
                  & r1_tarski(X1,X2) )
               => r1_tarski(X1,k3_subset_1(X0,X3)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_subset_1)).

fof(f2868,plain,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f1238])).

fof(f1238,axiom,(
    ! [X0,X1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relset_1)).

fof(f5114,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl206_3 ),
    inference(avatar_component_clause,[],[f5112])).

fof(f31106,plain,
    ( spl206_99
    | ~ spl206_3
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30817,f8733,f5112,f8717])).

fof(f30817,plain,
    ( r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f5114,f2878,f8735,f3676])).

fof(f31104,plain,
    ( spl206_587
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30833,f8733,f31101])).

fof(f31101,plain,
    ( spl206_587
  <=> r1_xboole_0(k10_relat_1(sK89,k1_xboole_0),k10_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_587])])).

fof(f30833,plain,
    ( r1_xboole_0(k10_relat_1(sK89,k1_xboole_0),k10_relat_1(sK89,sK3))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f8735,f3688])).

fof(f3688,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1851])).

fof(f1851,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          | ~ r1_xboole_0(X1,X2) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1850])).

fof(f1850,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2))
          | ~ r1_xboole_0(X1,X2) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f960])).

fof(f960,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_xboole_0(X1,X2)
         => r1_xboole_0(k10_relat_1(X0,X1),k10_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

fof(f3463,plain,(
    v1_funct_1(sK89) ),
    inference(cnf_transformation,[],[f2441])).

fof(f31099,plain,
    ( spl206_586
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30834,f8733,f31096])).

fof(f31096,plain,
    ( spl206_586
  <=> r1_xboole_0(k10_relat_1(sK162,k1_xboole_0),k10_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_586])])).

fof(f30834,plain,
    ( r1_xboole_0(k10_relat_1(sK162,k1_xboole_0),k10_relat_1(sK162,sK3))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f8735,f3688])).

fof(f31085,plain,
    ( spl206_585
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30850,f8733,f31082])).

fof(f31082,plain,
    ( spl206_585
  <=> sK3 = k3_tarski(k2_tarski(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_585])])).

fof(f30850,plain,
    ( sK3 = k3_tarski(k2_tarski(k1_xboole_0,sK3))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3491,f4641,f8735,f4602])).

fof(f4602,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k3_tarski(k2_tarski(X0,X1)) != k3_tarski(k2_tarski(X2,X3)) ) ),
    inference(definition_unfolding,[],[f3260,f3631,f3631])).

fof(f3260,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(cnf_transformation,[],[f1596])).

fof(f1596,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f1595])).

fof(f1595,plain,(
    ! [X0,X1,X2,X3] :
      ( X1 = X2
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_xboole_0(X2,X0)
      | k2_xboole_0(X0,X1) != k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f140])).

fof(f140,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f4641,plain,(
    ! [X0] : k3_tarski(k2_tarski(X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f3299,f3631])).

fof(f3299,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3491,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f30996,plain,
    ( spl206_583
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30995,f8733,f30979])).

fof(f30979,plain,
    ( spl206_583
  <=> r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_583])])).

fof(f30995,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30882,f4635])).

fof(f30882,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4948,f8735,f4620])).

fof(f4620,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_tarski(k2_tarski(X1,X2))) ) ),
    inference(definition_unfolding,[],[f3276,f3631])).

fof(f3276,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f1612])).

fof(f1612,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f138])).

fof(f138,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4948,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f3486])).

fof(f3486,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f1761])).

fof(f1761,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f132])).

fof(f132,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f30994,plain,
    ( spl206_584
    | ~ spl206_45
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30993,f8733,f7635,f30985])).

fof(f30985,plain,
    ( spl206_584
  <=> r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_584])])).

fof(f7635,plain,
    ( spl206_45
  <=> r1_xboole_0(k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_45])])).

fof(f30993,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK1,sK3)))
    | ~ spl206_45
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30883,f4635])).

fof(f30883,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK1)))
    | ~ spl206_45
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f7637,f8735,f4620])).

fof(f7637,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl206_45 ),
    inference(avatar_component_clause,[],[f7635])).

fof(f30991,plain,
    ( spl206_583
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30990,f8733,f30979])).

fof(f30990,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_102 ),
    inference(forward_demodulation,[],[f30885,f4635])).

fof(f30885,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK3,k1_xboole_0)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3491,f8735,f4620])).

fof(f30989,plain,
    ( spl206_583
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30886,f8733,f30979])).

fof(f30886,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f4948,f8735,f4620])).

fof(f30988,plain,
    ( spl206_584
    | ~ spl206_45
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30887,f8733,f7635,f30985])).

fof(f30887,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK1,sK3)))
    | ~ spl206_45
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f7637,f8735,f4620])).

fof(f30982,plain,
    ( spl206_583
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30889,f8733,f30979])).

fof(f30889,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f3491,f8735,f4620])).

fof(f30977,plain,
    ( spl206_582
    | ~ spl206_102 ),
    inference(avatar_split_clause,[],[f30890,f8733,f30974])).

fof(f30974,plain,
    ( spl206_582
  <=> k1_xboole_0 = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_582])])).

fof(f30890,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,sK3)),sK3)
    | ~ spl206_102 ),
    inference(unit_resulting_resolution,[],[f8735,f4629])).

fof(f4629,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k3_tarski(k2_tarski(X0,X1)),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f3287,f3631])).

fof(f3287,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1617])).

fof(f1617,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f158])).

fof(f158,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f30691,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29894,f8040,f30400])).

fof(f30400,plain,
    ( spl206_559
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_559])])).

fof(f8040,plain,
    ( spl206_72
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_72])])).

fof(f29894,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f2830,f8042,f2803])).

fof(f8042,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl206_72 ),
    inference(avatar_component_clause,[],[f8040])).

fof(f30690,plain,
    ( ~ spl206_581
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29897,f8040,f30687])).

fof(f30687,plain,
    ( spl206_581
  <=> r2_hidden(sK2,k2_relat_1(sK6(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_581])])).

fof(f29897,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4871,f8042,f2803])).

fof(f30685,plain,
    ( ~ spl206_557
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29900,f8040,f30387])).

fof(f30387,plain,
    ( spl206_557
  <=> r1_tarski(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_557])])).

fof(f29900,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4904,f8042,f2803])).

fof(f30658,plain,
    ( ~ spl206_580
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29936,f8040,f30655])).

fof(f30655,plain,
    ( spl206_580
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_580])])).

fof(f29936,plain,
    ( ~ m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4904,f8042,f2852])).

fof(f30627,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29972,f8040,f30400])).

fof(f29972,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f2878,f8042,f2852])).

fof(f30625,plain,
    ( ~ spl206_579
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29974,f8040,f30622])).

fof(f30622,plain,
    ( spl206_579
  <=> r2_hidden(sK2,sK19(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_579])])).

fof(f29974,plain,
    ( ~ r2_hidden(sK2,sK19(sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f2869,f8042,f2852])).

fof(f30620,plain,
    ( ~ spl206_578
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29975,f8040,f30617])).

fof(f30617,plain,
    ( spl206_578
  <=> r2_hidden(sK2,sK20(k1_zfmisc_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_578])])).

fof(f29975,plain,
    ( ~ r2_hidden(sK2,sK20(k1_zfmisc_1(sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f2871,f8042,f2852])).

fof(f30615,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30614,f8040,f30400])).

fof(f30614,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30613,f3391])).

fof(f30613,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k1_xboole_0))
    | spl206_72 ),
    inference(forward_demodulation,[],[f29980,f3060])).

fof(f29980,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(k1_xboole_0,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f8042,f2991])).

fof(f30612,plain,
    ( ~ spl206_577
    | spl206_72
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29988,f8752,f8040,f30609])).

fof(f30609,plain,
    ( spl206_577
  <=> r2_hidden(sK2,k1_relat_1(k7_relat_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_577])])).

fof(f29988,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK3,sK1)))
    | spl206_72
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8042,f2991])).

fof(f30607,plain,
    ( ~ spl206_576
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29995,f8040,f30604])).

fof(f30604,plain,
    ( spl206_576
  <=> r2_hidden(sK2,k1_relat_1(k7_relat_1(sK89,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_576])])).

fof(f29995,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK89,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3462,f8042,f2991])).

fof(f30602,plain,
    ( ~ spl206_575
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29996,f8040,f30599])).

fof(f30599,plain,
    ( spl206_575
  <=> r2_hidden(sK2,k1_relat_1(k7_relat_1(sK128,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_575])])).

fof(f29996,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK128,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3572,f8042,f2991])).

fof(f30597,plain,
    ( ~ spl206_574
    | spl206_72 ),
    inference(avatar_split_clause,[],[f29997,f8040,f30594])).

fof(f30594,plain,
    ( spl206_574
  <=> r2_hidden(sK2,k1_relat_1(k7_relat_1(sK162,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_574])])).

fof(f29997,plain,
    ( ~ r2_hidden(sK2,k1_relat_1(k7_relat_1(sK162,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3900,f8042,f2991])).

fof(f30592,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30591,f8040,f30400])).

fof(f30591,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30590,f3392])).

fof(f30590,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k1_xboole_0))
    | spl206_72 ),
    inference(forward_demodulation,[],[f30002,f3803])).

fof(f30002,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,k1_xboole_0)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f8042,f3304])).

fof(f30589,plain,
    ( ~ spl206_573
    | spl206_72
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f30010,f8752,f8040,f30586])).

fof(f30586,plain,
    ( spl206_573
  <=> r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_573])])).

fof(f30010,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK3)))
    | spl206_72
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8042,f3304])).

fof(f30584,plain,
    ( ~ spl206_572
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30017,f8040,f30581])).

fof(f30581,plain,
    ( spl206_572
  <=> r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_572])])).

fof(f30017,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK89)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3462,f8042,f3304])).

fof(f30579,plain,
    ( ~ spl206_571
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30018,f8040,f30576])).

fof(f30576,plain,
    ( spl206_571
  <=> r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_571])])).

fof(f30018,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK128)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3572,f8042,f3304])).

fof(f30574,plain,
    ( ~ spl206_570
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30019,f8040,f30571])).

fof(f30571,plain,
    ( spl206_570
  <=> r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_570])])).

fof(f30019,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k8_relat_1(sK1,sK162)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3900,f8042,f3304])).

fof(f30569,plain,
    ( spl206_569
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30070,f8040,f30564])).

fof(f30564,plain,
    ( spl206_569
  <=> sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK177(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_569])])).

fof(f30070,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK177(sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3609])).

fof(f30568,plain,
    ( spl206_551
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30071,f8040,f30346])).

fof(f30346,plain,
    ( spl206_551
  <=> sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_551])])).

fof(f30071,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3609])).

fof(f30567,plain,
    ( spl206_569
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30562,f8040,f30564])).

fof(f30562,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK177(sK1)))
    | spl206_72 ),
    inference(forward_demodulation,[],[f30072,f3634])).

fof(f30072,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK177(sK1),sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3609])).

fof(f30561,plain,
    ( spl206_551
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30073,f8040,f30346])).

fof(f30073,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3609])).

fof(f30560,plain,
    ( spl206_568
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30074,f8040,f30550])).

fof(f30550,plain,
    ( spl206_568
  <=> r1_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_568])])).

fof(f30074,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3610])).

fof(f30559,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30075,f8040,f30333])).

fof(f30333,plain,
    ( spl206_549
  <=> r1_xboole_0(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_549])])).

fof(f30075,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3610])).

fof(f30558,plain,
    ( spl206_568
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30557,f8040,f30550])).

fof(f30557,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30076,f3634])).

fof(f30076,plain,
    ( r1_xboole_0(k2_tarski(sK177(sK1),sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3610])).

fof(f30556,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30077,f8040,f30333])).

fof(f30077,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3610])).

fof(f30555,plain,
    ( spl206_568
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30078,f8040,f30550])).

fof(f30078,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3611])).

fof(f30554,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30079,f8040,f30333])).

fof(f30079,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3611])).

fof(f30553,plain,
    ( spl206_568
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30548,f8040,f30550])).

fof(f30548,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30080,f3634])).

fof(f30080,plain,
    ( r1_xboole_0(k2_tarski(sK177(sK1),sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3611])).

fof(f30547,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30081,f8040,f30333])).

fof(f30081,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3611])).

fof(f30546,plain,
    ( spl206_567
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30082,f8040,f30541])).

fof(f30541,plain,
    ( spl206_567
  <=> k2_tarski(sK2,sK177(sK1)) = k4_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_567])])).

fof(f30082,plain,
    ( k2_tarski(sK2,sK177(sK1)) = k4_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3615])).

fof(f30545,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30083,f8040,f30309])).

fof(f30309,plain,
    ( spl206_546
  <=> k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_546])])).

fof(f30083,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3615])).

fof(f30544,plain,
    ( spl206_567
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30539,f8040,f30541])).

fof(f30539,plain,
    ( k2_tarski(sK2,sK177(sK1)) = k4_xboole_0(k2_tarski(sK2,sK177(sK1)),sK1)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30084,f3634])).

fof(f30084,plain,
    ( k2_tarski(sK177(sK1),sK2) = k4_xboole_0(k2_tarski(sK177(sK1),sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f3615])).

fof(f30538,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30085,f8040,f30309])).

fof(f30085,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f3615])).

fof(f30537,plain,
    ( ~ spl206_566
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30088,f8040,f30534])).

fof(f30534,plain,
    ( spl206_566
  <=> r2_hidden(sK2,k3_relat_1(k2_wellord1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_566])])).

fof(f30088,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(k2_wellord1(k1_xboole_0,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f8042,f3743])).

fof(f30532,plain,
    ( ~ spl206_565
    | spl206_72
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f30096,f8752,f8040,f30529])).

fof(f30529,plain,
    ( spl206_565
  <=> r2_hidden(sK2,k3_relat_1(k2_wellord1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_565])])).

fof(f30096,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(k2_wellord1(sK3,sK1)))
    | spl206_72
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8042,f3743])).

fof(f30527,plain,
    ( ~ spl206_564
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30103,f8040,f30524])).

fof(f30524,plain,
    ( spl206_564
  <=> r2_hidden(sK2,k3_relat_1(k2_wellord1(sK89,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_564])])).

fof(f30103,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(k2_wellord1(sK89,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3462,f8042,f3743])).

fof(f30522,plain,
    ( ~ spl206_563
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30104,f8040,f30519])).

fof(f30519,plain,
    ( spl206_563
  <=> r2_hidden(sK2,k3_relat_1(k2_wellord1(sK128,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_563])])).

fof(f30104,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(k2_wellord1(sK128,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3572,f8042,f3743])).

fof(f30517,plain,
    ( ~ spl206_562
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30105,f8040,f30514])).

fof(f30514,plain,
    ( spl206_562
  <=> r2_hidden(sK2,k3_relat_1(k2_wellord1(sK162,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_562])])).

fof(f30105,plain,
    ( ~ r2_hidden(sK2,k3_relat_1(k2_wellord1(sK162,sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f3900,f8042,f3743])).

fof(f30512,plain,
    ( ~ spl206_561
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30110,f8040,f30509])).

fof(f30509,plain,
    ( spl206_561
  <=> r2_hidden(sK2,sK175(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_561])])).

fof(f30110,plain,
    ( ~ r2_hidden(sK2,sK175(sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4015])).

fof(f30507,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30506,f8040,f30400])).

fof(f30506,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30111,f4061])).

fof(f30111,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f4035])).

fof(f30505,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30504,f8040,f30400])).

fof(f30504,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30114,f4061])).

fof(f30114,plain,
    ( ~ r2_hidden(sK2,k5_xboole_0(sK1,sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f4035])).

fof(f30501,plain,
    ( spl206_560
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30500,f8040,f30435])).

fof(f30435,plain,
    ( spl206_560
  <=> r2_hidden(sK2,k5_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_560])])).

fof(f30500,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(forward_demodulation,[],[f30117,f4059])).

fof(f30117,plain,
    ( r2_hidden(sK2,k5_xboole_0(k2_tarski(sK2,sK2),sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4904,f8042,f4037])).

fof(f30438,plain,
    ( spl206_560
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30153,f8040,f30435])).

fof(f30153,plain,
    ( r2_hidden(sK2,k5_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4904,f8042,f4038])).

fof(f30407,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30406,f8040,f30400])).

fof(f30406,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30189,f3392])).

fof(f30189,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k1_xboole_0))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f4299,f8042,f4270])).

fof(f30405,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30404,f8040,f30400])).

fof(f30404,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30190,f3392])).

fof(f30190,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k1_xboole_0))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f4289,f8042,f4270])).

fof(f30403,plain,
    ( ~ spl206_559
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30398,f8040,f30400])).

fof(f30398,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30191,f3392])).

fof(f30191,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(k1_xboole_0))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4298,f4287,f8042,f4270])).

fof(f30396,plain,
    ( ~ spl206_558
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30195,f8040,f30393])).

fof(f30393,plain,
    ( spl206_558
  <=> r2_hidden(sK2,k2_relat_1(sK204(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_558])])).

fof(f30195,plain,
    ( ~ r2_hidden(sK2,k2_relat_1(sK204(sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4290,f4291,f8042,f4270])).

fof(f30391,plain,
    ( ~ spl206_557
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30196,f8040,f30387])).

fof(f30196,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4349])).

fof(f30390,plain,
    ( ~ spl206_557
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30197,f8040,f30387])).

fof(f30197,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4351])).

fof(f30385,plain,
    ( ~ spl206_556
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30384,f8040,f30380])).

fof(f30380,plain,
    ( spl206_556
  <=> r1_tarski(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_556])])).

fof(f30384,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),sK1)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30198,f4635])).

fof(f30198,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK1)),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4358])).

fof(f30383,plain,
    ( ~ spl206_556
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30378,f8040,f30380])).

fof(f30378,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),sK1)
    | spl206_72 ),
    inference(forward_demodulation,[],[f30199,f4635])).

fof(f30199,plain,
    ( ~ r1_tarski(k3_tarski(k2_tarski(k2_tarski(sK2,sK2),sK1)),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4359])).

fof(f30377,plain,
    ( ~ spl206_555
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30202,f8040,f30373])).

fof(f30373,plain,
    ( spl206_555
  <=> k2_tarski(sK2,sK2) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_555])])).

fof(f30202,plain,
    ( k2_tarski(sK2,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4450])).

fof(f30376,plain,
    ( ~ spl206_555
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30203,f8040,f30373])).

fof(f30203,plain,
    ( k2_tarski(sK2,sK2) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4451])).

fof(f30371,plain,
    ( spl206_554
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30205,f8040,f30363])).

fof(f30363,plain,
    ( spl206_554
  <=> r1_tarski(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_554])])).

fof(f30205,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4882,f8042,f4493])).

fof(f30370,plain,
    ( spl206_554
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30206,f8040,f30363])).

fof(f30206,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4881,f8042,f4493])).

fof(f30369,plain,
    ( spl206_553
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30207,f8040,f30358])).

fof(f30358,plain,
    ( spl206_553
  <=> r1_tarski(sK1,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK1)),k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_553])])).

fof(f30207,plain,
    ( r1_tarski(sK1,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK1)),k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4083,f8042,f4493])).

fof(f30368,plain,
    ( spl206_552
    | ~ spl206_2
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30209,f8040,f5107,f30353])).

fof(f30353,plain,
    ( spl206_552
  <=> r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_552])])).

fof(f30209,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ spl206_2
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f5109,f8042,f4493])).

fof(f30367,plain,
    ( spl206_554
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30210,f8040,f30363])).

fof(f30210,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4882,f8042,f4494])).

fof(f30366,plain,
    ( spl206_554
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30211,f8040,f30363])).

fof(f30211,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4881,f8042,f4494])).

fof(f30361,plain,
    ( spl206_553
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30212,f8040,f30358])).

fof(f30212,plain,
    ( r1_tarski(sK1,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK1)),k2_tarski(sK2,sK2)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4083,f8042,f4494])).

fof(f30356,plain,
    ( spl206_552
    | ~ spl206_2
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30214,f8040,f5107,f30353])).

fof(f30214,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK2,sK2)))
    | ~ spl206_2
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f5109,f8042,f4494])).

fof(f30351,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30215,f8040,f30309])).

fof(f30215,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4506])).

fof(f30350,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30216,f8040,f30309])).

fof(f30216,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4508])).

fof(f30349,plain,
    ( spl206_551
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30217,f8040,f30346])).

fof(f30217,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4510])).

fof(f30344,plain,
    ( ~ spl206_550
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30218,f8040,f30340])).

fof(f30340,plain,
    ( spl206_550
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_550])])).

fof(f30218,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4513])).

fof(f30343,plain,
    ( ~ spl206_550
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30219,f8040,f30340])).

fof(f30219,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4515])).

fof(f30338,plain,
    ( spl206_547
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30220,f8040,f30320])).

fof(f30320,plain,
    ( spl206_547
  <=> sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),k2_tarski(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_547])])).

fof(f30220,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4522])).

fof(f30337,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30221,f8040,f30333])).

fof(f30221,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4523])).

fof(f30336,plain,
    ( spl206_549
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30222,f8040,f30333])).

fof(f30222,plain,
    ( r1_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4524])).

fof(f30331,plain,
    ( spl206_548
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30224,f8040,f30326])).

fof(f30326,plain,
    ( spl206_548
  <=> sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK177(sK1)))),k2_tarski(sK2,sK177(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_548])])).

fof(f30224,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK177(sK1)))),k2_tarski(sK2,sK177(sK1)))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f4609])).

fof(f30330,plain,
    ( spl206_547
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30225,f8040,f30320])).

fof(f30225,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f4609])).

fof(f30329,plain,
    ( spl206_548
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30324,f8040,f30326])).

fof(f30324,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK177(sK1)))),k2_tarski(sK2,sK177(sK1)))
    | spl206_72 ),
    inference(forward_demodulation,[],[f30226,f3634])).

fof(f30226,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK177(sK1),sK2))),k2_tarski(sK177(sK1),sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4021,f8042,f4609])).

fof(f30323,plain,
    ( spl206_547
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30227,f8040,f30320])).

fof(f30227,plain,
    ( sK1 = k4_xboole_0(k3_tarski(k2_tarski(sK1,k2_tarski(sK2,sK2))),k2_tarski(sK2,sK2))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f8042,f4609])).

fof(f30313,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30237,f8040,f30309])).

fof(f30237,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4906])).

fof(f30312,plain,
    ( spl206_546
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30238,f8040,f30309])).

fof(f30238,plain,
    ( k2_tarski(sK2,sK2) = k4_xboole_0(k2_tarski(sK2,sK2),sK1)
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f8042,f4907])).

fof(f30307,plain,
    ( spl206_545
    | spl206_72 ),
    inference(avatar_split_clause,[],[f30240,f8040,f30304])).

fof(f30304,plain,
    ( spl206_545
  <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_545])])).

fof(f30240,plain,
    ( r2_hidden(sK2,k4_xboole_0(k2_tarski(sK2,sK2),sK1))
    | spl206_72 ),
    inference(unit_resulting_resolution,[],[f4904,f8042,f4980])).

fof(f29891,plain,
    ( ~ spl206_3
    | ~ spl206_544
    | spl206_1 ),
    inference(avatar_split_clause,[],[f29886,f5102,f29888,f5112])).

fof(f29888,plain,
    ( spl206_544
  <=> r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_544])])).

fof(f5102,plain,
    ( spl206_1
  <=> r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_1])])).

fof(f29886,plain,
    ( ~ r2_relset_1(sK1,sK0,k7_relat_1(sK3,sK2),sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl206_1 ),
    inference(superposition,[],[f5104,f2756])).

fof(f2756,plain,(
    ! [X2,X0,X3,X1] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1273])).

fof(f1273,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1224])).

fof(f1224,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f5104,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    | spl206_1 ),
    inference(avatar_component_clause,[],[f5102])).

fof(f29883,plain,
    ( spl206_543
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8871,f8752,f29876])).

fof(f29876,plain,
    ( spl206_543
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_543])])).

fof(f8871,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f4882,f8754,f2845])).

fof(f2845,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1335])).

fof(f1335,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1334])).

fof(f1334,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1230])).

fof(f1230,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

fof(f29882,plain,
    ( spl206_543
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8872,f8752,f29876])).

fof(f8872,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f4882,f8754,f2845])).

fof(f29881,plain,
    ( spl206_542
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8873,f8752,f29871])).

fof(f29871,plain,
    ( spl206_542
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_zfmisc_1(k3_tarski(k2_relat_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_542])])).

fof(f8873,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f4882,f8754,f2845])).

fof(f29880,plain,
    ( spl206_543
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8875,f8752,f29876])).

fof(f8875,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f4881,f8754,f2845])).

fof(f29879,plain,
    ( spl206_543
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8876,f8752,f29876])).

fof(f8876,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f4881,f8754,f2845])).

fof(f29874,plain,
    ( spl206_542
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8877,f8752,f29871])).

fof(f8877,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f4881,f8754,f2845])).

fof(f29869,plain,
    ( spl206_541
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8879,f8752,f29865])).

fof(f29865,plain,
    ( spl206_541
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_541])])).

fof(f8879,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f4083,f8754,f2845])).

fof(f29868,plain,
    ( spl206_541
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8880,f8752,f29865])).

fof(f8880,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f4083,f8754,f2845])).

fof(f29863,plain,
    ( spl206_540
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8881,f8752,f29860])).

fof(f29860,plain,
    ( spl206_540
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),k1_zfmisc_1(k3_tarski(k2_relat_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_540])])).

fof(f8881,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f4083,f8754,f2845])).

fof(f29857,plain,
    ( spl206_539
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8889,f8752,f29854])).

fof(f29854,plain,
    ( spl206_539
  <=> v1_relat_1(sK19(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_539])])).

fof(f8889,plain,
    ( v1_relat_1(sK19(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f2869,f8754,f2873])).

fof(f2873,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1358])).

fof(f1358,plain,(
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

fof(f29852,plain,
    ( spl206_538
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8890,f8752,f29849])).

fof(f29849,plain,
    ( spl206_538
  <=> v1_relat_1(sK20(k1_zfmisc_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_538])])).

fof(f8890,plain,
    ( v1_relat_1(sK20(k1_zfmisc_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f2871,f8754,f2873])).

fof(f29847,plain,
    ( spl206_537
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8891,f8752,f29844])).

fof(f29844,plain,
    ( spl206_537
  <=> r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_537])])).

fof(f8891,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2976])).

fof(f2976,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1400])).

fof(f1400,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f825])).

fof(f825,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f29840,plain,
    ( spl206_534
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8934,f8752,f5107,f29767])).

fof(f29767,plain,
    ( spl206_534
  <=> r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_534])])).

fof(f8934,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f2990])).

fof(f2990,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1414])).

fof(f1414,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1413])).

fof(f1413,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f711])).

fof(f711,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

fof(f29837,plain,
    ( spl206_534
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f8977,f8752,f5107,f29767])).

fof(f8977,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f2990])).

fof(f29834,plain,
    ( spl206_534
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9020,f8752,f5107,f29767])).

fof(f9020,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f2990])).

fof(f29831,plain,
    ( spl206_534
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9063,f8752,f5107,f29767])).

fof(f9063,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f2990])).

fof(f29784,plain,
    ( spl206_536
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9153,f8752,f5107,f29781])).

fof(f29781,plain,
    ( spl206_536
  <=> k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_536])])).

fof(f9153,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK1),sK2)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f2994])).

fof(f2994,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1417])).

fof(f1417,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1416])).

fof(f1416,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f707])).

fof(f707,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

fof(f29777,plain,
    ( spl206_535
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9196,f8752,f5107,f29774])).

fof(f29774,plain,
    ( spl206_535
  <=> k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_535])])).

fof(f9196,plain,
    ( k7_relat_1(sK3,sK1) = k7_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f2995])).

fof(f2995,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1419])).

fof(f1419,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1418])).

fof(f1418,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f708])).

fof(f708,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

fof(f29770,plain,
    ( spl206_534
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9239,f8752,f5107,f29767])).

fof(f9239,plain,
    ( r1_tarski(k7_relat_1(sK3,sK1),k7_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f2996])).

fof(f2996,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1421])).

fof(f1421,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1420])).

fof(f1420,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f709])).

fof(f709,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_relat_1)).

fof(f29764,plain,
    ( spl206_533
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9246,f8752,f29761])).

fof(f29761,plain,
    ( spl206_533
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_533])])).

fof(f9246,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4948,f8754,f2997])).

fof(f29759,plain,
    ( spl206_532
    | ~ spl206_45
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9247,f8752,f7635,f29756])).

fof(f29756,plain,
    ( spl206_532
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_532])])).

fof(f9247,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,k1_xboole_0),sK1)
    | ~ spl206_45
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f7637,f8754,f2997])).

fof(f29754,plain,
    ( spl206_531
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9252,f8752,f29751])).

fof(f29751,plain,
    ( spl206_531
  <=> v1_xboole_0(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_531])])).

fof(f9252,plain,
    ( v1_xboole_0(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3011])).

fof(f3011,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1441])).

fof(f1441,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1440])).

fof(f1440,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f685])).

fof(f685,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc16_relat_1)).

fof(f3492,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f29749,plain,
    ( spl206_530
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9253,f8752,f29746])).

fof(f29746,plain,
    ( spl206_530
  <=> v1_xboole_0(k7_relat_1(sK3,sK129)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_530])])).

fof(f9253,plain,
    ( v1_xboole_0(k7_relat_1(sK3,sK129))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3011])).

fof(f3573,plain,(
    v1_xboole_0(sK129) ),
    inference(cnf_transformation,[],[f2524])).

fof(f2524,plain,(
    v1_xboole_0(sK129) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK129])],[f26,f2523])).

fof(f2523,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK129) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

fof(f29744,plain,
    ( spl206_529
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9255,f8752,f29741])).

fof(f29741,plain,
    ( spl206_529
  <=> v1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_529])])).

fof(f9255,plain,
    ( v1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3012])).

fof(f3012,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1441])).

fof(f29739,plain,
    ( spl206_528
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9256,f8752,f29736])).

fof(f29736,plain,
    ( spl206_528
  <=> v1_relat_1(k7_relat_1(sK3,sK129)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_528])])).

fof(f9256,plain,
    ( v1_relat_1(k7_relat_1(sK3,sK129))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3012])).

fof(f29734,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9257,f8752,f29676])).

fof(f29676,plain,
    ( spl206_521
  <=> r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_521])])).

fof(f9257,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4882,f8754,f3015])).

fof(f3015,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k7_relat_1(X1,X0))
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1445])).

fof(f1445,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1444])).

fof(f1444,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k7_relat_1(X1,X0))
          | ~ r1_tarski(X2,X1)
          | ~ r1_tarski(k1_relat_1(X2),X0)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f788])).

fof(f788,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( ( r1_tarski(X2,X1)
              & r1_tarski(k1_relat_1(X2),X0) )
           => r1_tarski(X2,k7_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t186_relat_1)).

fof(f29733,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9258,f8752,f29676])).

fof(f9258,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4882,f8754,f3015])).

fof(f29732,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9260,f8752,f29676])).

fof(f9260,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4881,f8754,f3015])).

fof(f29731,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9261,f8752,f29676])).

fof(f9261,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4881,f8754,f3015])).

fof(f29730,plain,
    ( spl206_527
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9263,f8752,f29720])).

fof(f29720,plain,
    ( spl206_527
  <=> r1_tarski(sK3,k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_527])])).

fof(f9263,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4083,f8754,f3015])).

fof(f29729,plain,
    ( spl206_527
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9264,f8752,f29720])).

fof(f9264,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4083,f8754,f3015])).

fof(f29728,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9269,f8752,f29676])).

fof(f9269,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4882,f8754,f3015])).

fof(f29727,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9270,f8752,f29676])).

fof(f9270,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4882,f8754,f3015])).

fof(f29726,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9271,f8752,f29676])).

fof(f9271,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4881,f8754,f3015])).

fof(f29725,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9272,f8752,f29676])).

fof(f9272,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4881,f8754,f3015])).

fof(f29724,plain,
    ( spl206_527
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9273,f8752,f29720])).

fof(f9273,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f4083,f8754,f3015])).

fof(f29723,plain,
    ( spl206_527
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9274,f8752,f29720])).

fof(f9274,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f4083,f8754,f3015])).

fof(f29714,plain,
    ( spl206_512
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9416,f8752,f29605])).

fof(f29605,plain,
    ( spl206_512
  <=> k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_512])])).

fof(f9416,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3491,f8754,f3023])).

fof(f3023,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2294,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1455])).

fof(f1455,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f884])).

fof(f884,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f29713,plain,
    ( spl206_513
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9417,f8752,f29610])).

fof(f29610,plain,
    ( spl206_513
  <=> sK3 = k7_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_513])])).

fof(f9417,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3024])).

fof(f3024,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1457])).

fof(f1457,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1456])).

fof(f1456,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f886])).

fof(f886,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k7_relat_1(X1,X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

fof(f29712,plain,
    ( spl206_513
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9418,f8752,f29610])).

fof(f9418,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3024])).

fof(f29711,plain,
    ( spl206_526
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9419,f8752,f29708])).

fof(f29708,plain,
    ( spl206_526
  <=> sK3 = k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_526])])).

fof(f9419,plain,
    ( sK3 = k7_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f3024])).

fof(f29706,plain,
    ( spl206_525
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9421,f8752,f29702])).

fof(f29702,plain,
    ( spl206_525
  <=> k1_relat_1(sK3) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_525])])).

fof(f9421,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3025])).

fof(f3025,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1459])).

fof(f1459,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1458])).

fof(f1458,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f880])).

fof(f880,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

fof(f29705,plain,
    ( spl206_525
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9422,f8752,f29702])).

fof(f9422,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3025])).

fof(f29700,plain,
    ( spl206_524
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9423,f8752,f29697])).

fof(f29697,plain,
    ( spl206_524
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_524])])).

fof(f9423,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f2830,f8754,f3025])).

fof(f29695,plain,
    ( spl206_523
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9426,f8752,f29692])).

fof(f29692,plain,
    ( spl206_523
  <=> k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_523])])).

fof(f9426,plain,
    ( k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)) = k1_relat_1(k7_relat_1(sK3,k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4871,f8754,f3025])).

fof(f29688,plain,
    ( spl206_522
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9481,f8752,f5107,f29685])).

fof(f29685,plain,
    ( spl206_522
  <=> k9_relat_1(sK3,sK1) = k9_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_522])])).

fof(f9481,plain,
    ( k9_relat_1(sK3,sK1) = k9_relat_1(k7_relat_1(sK3,sK2),sK1)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3045])).

fof(f3045,plain,(
    ! [X2,X0,X1] :
      ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1480])).

fof(f1480,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1)
          | ~ r1_tarski(X1,X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f766])).

fof(f766,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => k9_relat_1(X0,X1) = k9_relat_1(k7_relat_1(X0,X2),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

fof(f29682,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9484,f8752,f29676])).

fof(f9484,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f8754,f3055])).

fof(f3055,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2306])).

fof(f2306,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tarski(X0,X1)
              | ~ r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
            & ( r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0)))
              | ~ r1_tarski(X0,X1) ) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1487])).

fof(f1487,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f824])).

fof(f824,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
          <=> r1_tarski(X0,k7_relat_1(X1,k1_relat_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t219_relat_1)).

fof(f29681,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9485,f8752,f29676])).

fof(f9485,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f8754,f3055])).

fof(f29680,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9486,f8752,f29676])).

fof(f9486,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f8754,f3055])).

fof(f29679,plain,
    ( spl206_521
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9487,f8752,f29676])).

fof(f9487,plain,
    ( r1_tarski(sK3,k7_relat_1(sK3,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f8754,f3055])).

fof(f29670,plain,
    ( spl206_517
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9498,f8752,f29638])).

fof(f29638,plain,
    ( spl206_517
  <=> k7_relat_1(sK3,k1_relat_1(sK3)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_517])])).

fof(f9498,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3057])).

fof(f3057,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1488])).

fof(f1488,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0))))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f791])).

fof(f791,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k7_relat_1(X0,k1_relat_1(X1)) = k7_relat_1(X0,k1_relat_1(k7_relat_1(X1,k1_relat_1(X0)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

fof(f29661,plain,
    ( spl206_520
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9505,f8752,f29658])).

fof(f29658,plain,
    ( spl206_520
  <=> k7_relat_1(sK3,k1_relat_1(sK89)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK89,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_520])])).

fof(f9505,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK89)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK89,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3057])).

fof(f29656,plain,
    ( spl206_519
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9506,f8752,f29653])).

fof(f29653,plain,
    ( spl206_519
  <=> k7_relat_1(sK3,k1_relat_1(sK128)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK128,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_519])])).

fof(f9506,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK128)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK128,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3057])).

fof(f29651,plain,
    ( spl206_518
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9507,f8752,f29648])).

fof(f29648,plain,
    ( spl206_518
  <=> k7_relat_1(sK3,k1_relat_1(sK162)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK162,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_518])])).

fof(f9507,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK162)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK162,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3057])).

fof(f29641,plain,
    ( spl206_517
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9520,f8752,f29638])).

fof(f9520,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = k7_relat_1(sK3,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3057])).

fof(f29628,plain,
    ( spl206_516
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9527,f8752,f29625])).

fof(f29625,plain,
    ( spl206_516
  <=> k7_relat_1(sK89,k1_relat_1(sK3)) = k7_relat_1(sK89,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_516])])).

fof(f9527,plain,
    ( k7_relat_1(sK89,k1_relat_1(sK3)) = k7_relat_1(sK89,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3057])).

fof(f29623,plain,
    ( spl206_515
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9528,f8752,f29620])).

fof(f29620,plain,
    ( spl206_515
  <=> k7_relat_1(sK128,k1_relat_1(sK3)) = k7_relat_1(sK128,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_515])])).

fof(f9528,plain,
    ( k7_relat_1(sK128,k1_relat_1(sK3)) = k7_relat_1(sK128,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3057])).

fof(f29618,plain,
    ( spl206_514
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9529,f8752,f29615])).

fof(f29615,plain,
    ( spl206_514
  <=> k7_relat_1(sK162,k1_relat_1(sK3)) = k7_relat_1(sK162,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_514])])).

fof(f9529,plain,
    ( k7_relat_1(sK162,k1_relat_1(sK3)) = k7_relat_1(sK162,k1_relat_1(k7_relat_1(sK3,k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3057])).

fof(f29613,plain,
    ( spl206_513
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9534,f8752,f29610])).

fof(f9534,plain,
    ( sK3 = k7_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3058])).

fof(f3058,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1489])).

fof(f1489,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f887])).

fof(f887,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

fof(f29608,plain,
    ( spl206_512
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9535,f8752,f29605])).

fof(f9535,plain,
    ( k1_xboole_0 = k7_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3059])).

fof(f3059,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1490])).

fof(f1490,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f715])).

fof(f715,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

fof(f29603,plain,
    ( spl206_403
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9544,f8752,f28562])).

fof(f28562,plain,
    ( spl206_403
  <=> k1_xboole_0 = k10_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_403])])).

fof(f9544,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3491,f8754,f3337])).

fof(f3337,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2382])).

fof(f2382,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1655])).

fof(f1655,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f775])).

fof(f775,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f29602,plain,
    ( spl206_479
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9545,f8752,f29348])).

fof(f29348,plain,
    ( spl206_479
  <=> sK3 = k5_relat_1(sK3,k6_relat_1(k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_479])])).

fof(f9545,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3338])).

fof(f3338,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1657])).

fof(f1657,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1656])).

fof(f1656,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f871])).

fof(f871,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f29601,plain,
    ( spl206_479
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9546,f8752,f29348])).

fof(f9546,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3338])).

fof(f29600,plain,
    ( spl206_511
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9547,f8752,f29597])).

fof(f29597,plain,
    ( spl206_511
  <=> sK3 = k5_relat_1(sK3,k6_relat_1(k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_511])])).

fof(f9547,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(k1_zfmisc_1(k3_tarski(k2_relat_1(sK3)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f3338])).

fof(f29595,plain,
    ( spl206_476
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9549,f8752,f29333])).

fof(f29333,plain,
    ( spl206_476
  <=> sK3 = k8_relat_1(k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_476])])).

fof(f9549,plain,
    ( sK3 = k8_relat_1(k2_relat_1(sK3),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3339])).

fof(f3339,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1659])).

fof(f1659,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1658])).

fof(f1658,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f728])).

fof(f728,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f29594,plain,
    ( spl206_476
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9550,f8752,f29333])).

fof(f9550,plain,
    ( sK3 = k8_relat_1(k2_relat_1(sK3),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3339])).

fof(f29593,plain,
    ( spl206_510
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9551,f8752,f29590])).

fof(f29590,plain,
    ( spl206_510
  <=> sK3 = k8_relat_1(k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_510])])).

fof(f9551,plain,
    ( sK3 = k8_relat_1(k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f3339])).

fof(f29588,plain,
    ( spl206_509
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9553,f8752,f29584])).

fof(f29584,plain,
    ( spl206_509
  <=> k2_relat_1(sK3) = k2_relat_1(k8_relat_1(k2_relat_1(sK3),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_509])])).

fof(f9553,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k8_relat_1(k2_relat_1(sK3),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3340])).

fof(f3340,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1661])).

fof(f1661,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1660])).

fof(f1660,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k8_relat_1(X0,X1)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f723])).

fof(f723,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k2_relat_1(k8_relat_1(X0,X1)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_relat_1)).

fof(f29587,plain,
    ( spl206_509
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9554,f8752,f29584])).

fof(f9554,plain,
    ( k2_relat_1(sK3) = k2_relat_1(k8_relat_1(k2_relat_1(sK3),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3340])).

fof(f29582,plain,
    ( spl206_508
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9555,f8752,f29579])).

fof(f29579,plain,
    ( spl206_508
  <=> k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_508])])).

fof(f9555,plain,
    ( k1_xboole_0 = k2_relat_1(k8_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f2830,f8754,f3340])).

fof(f29577,plain,
    ( spl206_507
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9558,f8752,f29574])).

fof(f29574,plain,
    ( spl206_507
  <=> k2_relat_1(sK6(k2_relat_1(sK3),k1_xboole_0)) = k2_relat_1(k8_relat_1(k2_relat_1(sK6(k2_relat_1(sK3),k1_xboole_0)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_507])])).

fof(f9558,plain,
    ( k2_relat_1(sK6(k2_relat_1(sK3),k1_xboole_0)) = k2_relat_1(k8_relat_1(k2_relat_1(sK6(k2_relat_1(sK3),k1_xboole_0)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4871,f8754,f3340])).

fof(f29572,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9565,f8752,f29534])).

fof(f29534,plain,
    ( spl206_506
  <=> k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_506])])).

fof(f9565,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3831,f3390,f8754,f3371])).

fof(f3371,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
      | k2_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1685])).

fof(f1685,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1684])).

fof(f1684,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2))
              | k2_relat_1(X0) != k2_relat_1(X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f802])).

fof(f802,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k2_relat_1(X0) = k2_relat_1(X1)
               => k2_relat_1(k5_relat_1(X0,X2)) = k2_relat_1(k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t199_relat_1)).

fof(f3390,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f863,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f29571,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9573,f8752,f29477])).

fof(f29477,plain,
    ( spl206_502
  <=> k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_502])])).

fof(f9573,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3390,f8754,f3371])).

fof(f29570,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9580,f8752,f29528])).

fof(f29528,plain,
    ( spl206_505
  <=> k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_505])])).

fof(f9580,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3390,f8754,f3371])).

fof(f29569,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9581,f8752,f29523])).

fof(f29523,plain,
    ( spl206_504
  <=> k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_504])])).

fof(f9581,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3390,f8754,f3371])).

fof(f29568,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9582,f8752,f29518])).

fof(f29518,plain,
    ( spl206_503
  <=> k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_503])])).

fof(f9582,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3390,f8754,f3371])).

fof(f29567,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9587,f8752,f29534])).

fof(f9587,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3827,f3390,f8754,f3371])).

fof(f3827,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f922])).

fof(f922,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f29566,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9595,f8752,f29477])).

fof(f9595,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3390,f8754,f3371])).

fof(f29565,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9602,f8752,f29528])).

fof(f9602,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3390,f8754,f3371])).

fof(f29564,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9603,f8752,f29523])).

fof(f9603,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3390,f8754,f3371])).

fof(f29563,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9604,f8752,f29518])).

fof(f9604,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3390,f8754,f3371])).

fof(f29562,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9609,f8752,f29534])).

fof(f9609,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3825,f3390,f8754,f3371])).

fof(f3825,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f921])).

fof(f921,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f29561,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9617,f8752,f29477])).

fof(f9617,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3390,f8754,f3371])).

fof(f29560,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9624,f8752,f29528])).

fof(f9624,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3390,f8754,f3371])).

fof(f29559,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9625,f8752,f29523])).

fof(f9625,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3390,f8754,f3371])).

fof(f29558,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9626,f8752,f29518])).

fof(f9626,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3390,f8754,f3371])).

fof(f29557,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9631,f8752,f29534])).

fof(f9631,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3822,f3390,f8754,f3371])).

fof(f3822,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f917])).

fof(f29556,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9639,f8752,f29477])).

fof(f9639,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3390,f8754,f3371])).

fof(f29555,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9646,f8752,f29528])).

fof(f9646,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3390,f8754,f3371])).

fof(f29554,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9647,f8752,f29523])).

fof(f9647,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3390,f8754,f3371])).

fof(f29553,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9648,f8752,f29518])).

fof(f9648,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3390,f8754,f3371])).

fof(f29552,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9653,f8752,f29534])).

fof(f9653,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3831,f3390,f8754,f3371])).

fof(f29551,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9661,f8752,f29477])).

fof(f9661,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3390,f8754,f3371])).

fof(f29550,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9668,f8752,f29528])).

fof(f9668,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3390,f8754,f3371])).

fof(f29549,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9669,f8752,f29523])).

fof(f9669,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3390,f8754,f3371])).

fof(f29548,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9670,f8752,f29518])).

fof(f9670,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3390,f8754,f3371])).

fof(f29547,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9675,f8752,f29534])).

fof(f9675,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3827,f3390,f8754,f3371])).

fof(f29546,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9683,f8752,f29477])).

fof(f9683,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3390,f8754,f3371])).

fof(f29545,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9690,f8752,f29528])).

fof(f9690,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3390,f8754,f3371])).

fof(f29544,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9691,f8752,f29523])).

fof(f9691,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3390,f8754,f3371])).

fof(f29543,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9692,f8752,f29518])).

fof(f9692,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3390,f8754,f3371])).

fof(f29542,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9697,f8752,f29534])).

fof(f9697,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3825,f3390,f8754,f3371])).

fof(f29541,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9705,f8752,f29477])).

fof(f9705,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3390,f8754,f3371])).

fof(f29540,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9712,f8752,f29528])).

fof(f9712,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3390,f8754,f3371])).

fof(f29539,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9713,f8752,f29523])).

fof(f9713,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3390,f8754,f3371])).

fof(f29538,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9714,f8752,f29518])).

fof(f9714,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3390,f8754,f3371])).

fof(f29537,plain,
    ( spl206_506
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9719,f8752,f29534])).

fof(f9719,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3822,f3390,f8754,f3371])).

fof(f29532,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9727,f8752,f29477])).

fof(f9727,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3390,f8754,f3371])).

fof(f29531,plain,
    ( spl206_505
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9734,f8752,f29528])).

fof(f9734,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3390,f8754,f3371])).

fof(f29526,plain,
    ( spl206_504
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9735,f8752,f29523])).

fof(f9735,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3390,f8754,f3371])).

fof(f29521,plain,
    ( spl206_503
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9736,f8752,f29518])).

fof(f9736,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3390,f8754,f3371])).

fof(f29515,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9749,f8752,f29477])).

fof(f9749,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3390,f8754,f3371])).

fof(f29514,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9756,f8752,f29472])).

fof(f29472,plain,
    ( spl206_501
  <=> k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_501])])).

fof(f9756,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3390,f8754,f3371])).

fof(f29513,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9757,f8752,f29467])).

fof(f29467,plain,
    ( spl206_500
  <=> k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_500])])).

fof(f9757,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3390,f8754,f3371])).

fof(f29512,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9758,f8752,f29462])).

fof(f29462,plain,
    ( spl206_499
  <=> k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_499])])).

fof(f9758,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3390,f8754,f3371])).

fof(f29510,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9771,f8752,f29477])).

fof(f9771,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3390,f8754,f3371])).

fof(f29509,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9778,f8752,f29472])).

fof(f9778,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3390,f8754,f3371])).

fof(f29508,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9779,f8752,f29467])).

fof(f9779,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3390,f8754,f3371])).

fof(f29507,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9780,f8752,f29462])).

fof(f9780,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3390,f8754,f3371])).

fof(f29505,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9793,f8752,f29477])).

fof(f9793,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3390,f8754,f3371])).

fof(f29504,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9800,f8752,f29472])).

fof(f9800,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3390,f8754,f3371])).

fof(f29503,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9801,f8752,f29467])).

fof(f9801,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3390,f8754,f3371])).

fof(f29502,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9802,f8752,f29462])).

fof(f9802,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3390,f8754,f3371])).

fof(f29500,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9815,f8752,f29477])).

fof(f9815,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3390,f8754,f3371])).

fof(f29499,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9822,f8752,f29472])).

fof(f9822,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3390,f8754,f3371])).

fof(f29498,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9823,f8752,f29467])).

fof(f9823,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3390,f8754,f3371])).

fof(f29497,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9824,f8752,f29462])).

fof(f9824,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3390,f8754,f3371])).

fof(f29495,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9837,f8752,f29477])).

fof(f9837,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3390,f8754,f3371])).

fof(f29494,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9844,f8752,f29472])).

fof(f9844,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3390,f8754,f3371])).

fof(f29493,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9845,f8752,f29467])).

fof(f9845,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3390,f8754,f3371])).

fof(f29492,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9846,f8752,f29462])).

fof(f9846,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3390,f8754,f3371])).

fof(f29490,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9859,f8752,f29477])).

fof(f9859,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3390,f8754,f3371])).

fof(f29489,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9866,f8752,f29472])).

fof(f9866,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3390,f8754,f3371])).

fof(f29488,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9867,f8752,f29467])).

fof(f9867,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3390,f8754,f3371])).

fof(f29487,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9868,f8752,f29462])).

fof(f9868,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3390,f8754,f3371])).

fof(f29485,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9881,f8752,f29477])).

fof(f9881,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3390,f8754,f3371])).

fof(f29484,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9888,f8752,f29472])).

fof(f9888,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3390,f8754,f3371])).

fof(f29483,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9889,f8752,f29467])).

fof(f9889,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3390,f8754,f3371])).

fof(f29482,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9890,f8752,f29462])).

fof(f9890,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3390,f8754,f3371])).

fof(f29480,plain,
    ( spl206_502
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9903,f8752,f29477])).

fof(f9903,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK3)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3390,f8754,f3371])).

fof(f29475,plain,
    ( spl206_501
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9910,f8752,f29472])).

fof(f9910,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK89)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3390,f8754,f3371])).

fof(f29470,plain,
    ( spl206_500
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9911,f8752,f29467])).

fof(f9911,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK128)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3390,f8754,f3371])).

fof(f29465,plain,
    ( spl206_499
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9912,f8752,f29462])).

fof(f9912,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k2_relat_1(k5_relat_1(k6_relat_1(k2_relat_1(sK162)),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3390,f8754,f3371])).

fof(f29460,plain,
    ( spl206_498
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29455,f8752,f29457])).

fof(f29457,plain,
    ( spl206_498
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_498])])).

fof(f29455,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0),sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f9918,f4872])).

fof(f4872,plain,(
    ! [X0] : k1_xboole_0 = k1_relat_1(sK6(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f2783])).

fof(f2783,plain,(
    ! [X0,X1] :
      ( k1_relat_1(sK6(X0,X1)) = X1
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2209])).

fof(f9918,plain,
    ( k1_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)) = k1_relat_1(k5_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0),sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4874,f4871,f8754,f3374])).

fof(f3374,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
      | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1691])).

fof(f1691,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1690])).

fof(f1690,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1))
          | ~ r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f845])).

fof(f845,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
           => k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_relat_1)).

fof(f4874,plain,(
    ! [X0] : v1_relat_1(sK6(X0,k1_xboole_0)) ),
    inference(equality_resolution,[],[f2779])).

fof(f2779,plain,(
    ! [X0,X1] :
      ( v1_relat_1(sK6(X0,X1))
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f2209])).

fof(f29454,plain,
    ( spl206_497
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29449,f8752,f29451])).

fof(f29451,plain,
    ( spl206_497
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_497])])).

fof(f29449,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f9920,f3490])).

fof(f3490,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f753])).

fof(f753,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f9920,plain,
    ( k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k9_relat_1(k1_xboole_0,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3377])).

fof(f3377,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1696])).

fof(f1696,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f764])).

fof(f764,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f29448,plain,
    ( spl206_492
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9928,f8752,f29419])).

fof(f29419,plain,
    ( spl206_492
  <=> k2_relat_1(k5_relat_1(sK3,sK3)) = k9_relat_1(sK3,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_492])])).

fof(f9928,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k9_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3377])).

fof(f29447,plain,
    ( spl206_496
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9935,f8752,f29444])).

fof(f29444,plain,
    ( spl206_496
  <=> k2_relat_1(k5_relat_1(sK3,sK89)) = k9_relat_1(sK89,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_496])])).

fof(f9935,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK89)) = k9_relat_1(sK89,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3377])).

fof(f29442,plain,
    ( spl206_495
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9936,f8752,f29439])).

fof(f29439,plain,
    ( spl206_495
  <=> k2_relat_1(k5_relat_1(sK3,sK128)) = k9_relat_1(sK128,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_495])])).

fof(f9936,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK128)) = k9_relat_1(sK128,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3377])).

fof(f29437,plain,
    ( spl206_494
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9937,f8752,f29434])).

fof(f29434,plain,
    ( spl206_494
  <=> k2_relat_1(k5_relat_1(sK3,sK162)) = k9_relat_1(sK162,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_494])])).

fof(f9937,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK162)) = k9_relat_1(sK162,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3377])).

fof(f29432,plain,
    ( spl206_493
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29427,f8752,f29429])).

fof(f29429,plain,
    ( spl206_493
  <=> k9_relat_1(sK3,k1_xboole_0) = k2_relat_1(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_493])])).

fof(f29427,plain,
    ( k9_relat_1(sK3,k1_xboole_0) = k2_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f9942,f3392])).

fof(f9942,plain,
    ( k2_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k9_relat_1(sK3,k2_relat_1(k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3377])).

fof(f29422,plain,
    ( spl206_492
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9950,f8752,f29419])).

fof(f9950,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK3)) = k9_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3377])).

fof(f29417,plain,
    ( spl206_491
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9957,f8752,f29414])).

fof(f29414,plain,
    ( spl206_491
  <=> k2_relat_1(k5_relat_1(sK89,sK3)) = k9_relat_1(sK3,k2_relat_1(sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_491])])).

fof(f9957,plain,
    ( k2_relat_1(k5_relat_1(sK89,sK3)) = k9_relat_1(sK3,k2_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3377])).

fof(f29412,plain,
    ( spl206_490
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9958,f8752,f29409])).

fof(f29409,plain,
    ( spl206_490
  <=> k2_relat_1(k5_relat_1(sK128,sK3)) = k9_relat_1(sK3,k2_relat_1(sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_490])])).

fof(f9958,plain,
    ( k2_relat_1(k5_relat_1(sK128,sK3)) = k9_relat_1(sK3,k2_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3377])).

fof(f29407,plain,
    ( spl206_489
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9959,f8752,f29404])).

fof(f29404,plain,
    ( spl206_489
  <=> k2_relat_1(k5_relat_1(sK162,sK3)) = k9_relat_1(sK3,k2_relat_1(sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_489])])).

fof(f9959,plain,
    ( k2_relat_1(k5_relat_1(sK162,sK3)) = k9_relat_1(sK3,k2_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3377])).

fof(f29402,plain,
    ( spl206_488
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29397,f8752,f29399])).

fof(f29399,plain,
    ( spl206_488
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_488])])).

fof(f29397,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_xboole_0)
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f9964,f3392])).

fof(f9964,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3378])).

fof(f3378,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1697])).

fof(f1697,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f844])).

fof(f844,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f29392,plain,
    ( spl206_483
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9972,f8752,f29368])).

fof(f29368,plain,
    ( spl206_483
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_483])])).

fof(f9972,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3378])).

fof(f29391,plain,
    ( spl206_487
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9979,f8752,f29388])).

fof(f29388,plain,
    ( spl206_487
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK89)),k2_relat_1(sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_487])])).

fof(f9979,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK89)),k2_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3378])).

fof(f29386,plain,
    ( spl206_486
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9980,f8752,f29383])).

fof(f29383,plain,
    ( spl206_486
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK128)),k2_relat_1(sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_486])])).

fof(f9980,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK128)),k2_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3378])).

fof(f29381,plain,
    ( spl206_485
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9981,f8752,f29378])).

fof(f29378,plain,
    ( spl206_485
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK3,sK162)),k2_relat_1(sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_485])])).

fof(f9981,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK162)),k2_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3378])).

fof(f29376,plain,
    ( spl206_484
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9986,f8752,f29373])).

fof(f29373,plain,
    ( spl206_484
  <=> r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_484])])).

fof(f9986,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(k1_xboole_0,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3378])).

fof(f29371,plain,
    ( spl206_483
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f9994,f8752,f29368])).

fof(f9994,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3378])).

fof(f29366,plain,
    ( spl206_482
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10001,f8752,f29363])).

fof(f29363,plain,
    ( spl206_482
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK89,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_482])])).

fof(f10001,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK89,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3378])).

fof(f29361,plain,
    ( spl206_481
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10002,f8752,f29358])).

fof(f29358,plain,
    ( spl206_481
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK128,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_481])])).

fof(f10002,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK128,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3378])).

fof(f29356,plain,
    ( spl206_480
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10003,f8752,f29353])).

fof(f29353,plain,
    ( spl206_480
  <=> r1_tarski(k2_relat_1(k5_relat_1(sK162,sK3)),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_480])])).

fof(f10003,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK162,sK3)),k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3378])).

fof(f29351,plain,
    ( spl206_479
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10008,f8752,f29348])).

fof(f10008,plain,
    ( sK3 = k5_relat_1(sK3,k6_relat_1(k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3384])).

fof(f3384,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1702])).

fof(f1702,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f872])).

fof(f872,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f29346,plain,
    ( spl206_478
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10009,f8752,f29343])).

fof(f29343,plain,
    ( spl206_478
  <=> k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_478])])).

fof(f10009,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3385])).

fof(f3385,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1703])).

fof(f1703,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f771])).

fof(f771,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

fof(f29341,plain,
    ( spl206_477
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10010,f8752,f29338])).

fof(f29338,plain,
    ( spl206_477
  <=> k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_477])])).

fof(f10010,plain,
    ( k2_relat_1(sK3) = k9_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3386])).

fof(f3386,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1704])).

fof(f1704,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f748])).

fof(f748,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

fof(f29336,plain,
    ( spl206_476
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10011,f8752,f29333])).

fof(f10011,plain,
    ( sK3 = k8_relat_1(k2_relat_1(sK3),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3387])).

fof(f3387,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1705])).

fof(f1705,plain,(
    ! [X0] :
      ( k8_relat_1(k2_relat_1(X0),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f729])).

fof(f729,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k8_relat_1(k2_relat_1(X0),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t126_relat_1)).

fof(f29331,plain,
    ( spl206_438
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10012,f8752,f28888])).

fof(f28888,plain,
    ( spl206_438
  <=> k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_438])])).

fof(f10012,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3491,f8754,f3416])).

fof(f3416,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2416])).

fof(f2416,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1721])).

fof(f1721,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f754])).

fof(f754,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f29330,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10014,f8752,f29282])).

fof(f29282,plain,
    ( spl206_475
  <=> k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_475])])).

fof(f10014,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3831,f3389,f8754,f3457])).

fof(f3457,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
      | k1_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1740])).

fof(f1740,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1739])).

fof(f1739,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1))
              | k1_relat_1(X1) != k1_relat_1(X0)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f801])).

fof(f801,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( k1_relat_1(X1) = k1_relat_1(X0)
               => k1_relat_1(k5_relat_1(X2,X0)) = k1_relat_1(k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t198_relat_1)).

fof(f3389,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f863])).

fof(f29329,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10022,f8752,f29073])).

fof(f29073,plain,
    ( spl206_463
  <=> k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_463])])).

fof(f10022,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3389,f8754,f3457])).

fof(f29328,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10029,f8752,f29276])).

fof(f29276,plain,
    ( spl206_474
  <=> k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_474])])).

fof(f10029,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3389,f8754,f3457])).

fof(f29327,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10030,f8752,f29271])).

fof(f29271,plain,
    ( spl206_473
  <=> k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_473])])).

fof(f10030,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3389,f8754,f3457])).

fof(f29326,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10031,f8752,f29266])).

fof(f29266,plain,
    ( spl206_472
  <=> k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_472])])).

fof(f10031,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3389,f8754,f3457])).

fof(f29325,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10036,f8752,f29282])).

fof(f10036,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3827,f3389,f8754,f3457])).

fof(f29324,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10044,f8752,f29073])).

fof(f10044,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3389,f8754,f3457])).

fof(f29323,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10051,f8752,f29276])).

fof(f10051,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3389,f8754,f3457])).

fof(f29322,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10052,f8752,f29271])).

fof(f10052,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3389,f8754,f3457])).

fof(f29321,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10053,f8752,f29266])).

fof(f10053,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3389,f8754,f3457])).

fof(f29320,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10058,f8752,f29282])).

fof(f10058,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3825,f3389,f8754,f3457])).

fof(f29319,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10066,f8752,f29073])).

fof(f10066,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3389,f8754,f3457])).

fof(f29318,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10073,f8752,f29276])).

fof(f10073,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3389,f8754,f3457])).

fof(f29317,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10074,f8752,f29271])).

fof(f10074,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3389,f8754,f3457])).

fof(f29316,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10075,f8752,f29266])).

fof(f10075,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3389,f8754,f3457])).

fof(f29315,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10080,f8752,f29282])).

fof(f10080,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3822,f3389,f8754,f3457])).

fof(f29314,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10088,f8752,f29073])).

fof(f10088,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3389,f8754,f3457])).

fof(f29313,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10095,f8752,f29276])).

fof(f10095,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3389,f8754,f3457])).

fof(f29312,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10096,f8752,f29271])).

fof(f10096,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3389,f8754,f3457])).

fof(f29311,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10097,f8752,f29266])).

fof(f10097,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3389,f8754,f3457])).

fof(f29310,plain,
    ( spl206_471
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10124,f8752,f29261])).

fof(f29261,plain,
    ( spl206_471
  <=> k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK79(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_471])])).

fof(f10124,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3418,f3420,f8754,f3457])).

fof(f3420,plain,(
    ! [X0] : k1_relat_1(sK79(X0)) = X0 ),
    inference(cnf_transformation,[],[f2418])).

fof(f2418,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK79(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK79(X0)) = X0
      & v1_funct_1(sK79(X0))
      & v1_relat_1(sK79(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK79])],[f1723,f2417])).

fof(f2417,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK79(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK79(X0)) = X0
        & v1_funct_1(sK79(X0))
        & v1_relat_1(sK79(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1723,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f941])).

fof(f941,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e2_25__funct_1)).

fof(f3418,plain,(
    ! [X0] : v1_relat_1(sK79(X0)) ),
    inference(cnf_transformation,[],[f2418])).

fof(f29309,plain,
    ( spl206_458
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10132,f8752,f29021])).

fof(f29021,plain,
    ( spl206_458
  <=> k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_458])])).

fof(f10132,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3418,f3420,f8754,f3457])).

fof(f29308,plain,
    ( spl206_470
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10139,f8752,f29255])).

fof(f29255,plain,
    ( spl206_470
  <=> k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK79(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_470])])).

fof(f10139,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3418,f3420,f8754,f3457])).

fof(f29307,plain,
    ( spl206_469
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10140,f8752,f29250])).

fof(f29250,plain,
    ( spl206_469
  <=> k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK79(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_469])])).

fof(f10140,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3418,f3420,f8754,f3457])).

fof(f29306,plain,
    ( spl206_468
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10141,f8752,f29245])).

fof(f29245,plain,
    ( spl206_468
  <=> k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK79(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_468])])).

fof(f10141,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3418,f3420,f8754,f3457])).

fof(f29305,plain,
    ( spl206_467
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10146,f8752,f29240])).

fof(f29240,plain,
    ( spl206_467
  <=> k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK80(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_467])])).

fof(f10146,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3422,f3424,f8754,f3457])).

fof(f3424,plain,(
    ! [X0] : k1_relat_1(sK80(X0)) = X0 ),
    inference(cnf_transformation,[],[f2420])).

fof(f2420,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK80(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK80(X0)) = X0
      & v1_funct_1(sK80(X0))
      & v1_relat_1(sK80(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK80])],[f1724,f2419])).

fof(f2419,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK80(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK80(X0)) = X0
        & v1_funct_1(sK80(X0))
        & v1_relat_1(sK80(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1724,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f944])).

fof(f944,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s3_funct_1__e9_44_1__funct_1)).

fof(f3422,plain,(
    ! [X0] : v1_relat_1(sK80(X0)) ),
    inference(cnf_transformation,[],[f2420])).

fof(f29304,plain,
    ( spl206_453
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10154,f8752,f28984])).

fof(f28984,plain,
    ( spl206_453
  <=> k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_453])])).

fof(f10154,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3422,f3424,f8754,f3457])).

fof(f29303,plain,
    ( spl206_466
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10161,f8752,f29234])).

fof(f29234,plain,
    ( spl206_466
  <=> k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK80(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_466])])).

fof(f10161,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3422,f3424,f8754,f3457])).

fof(f29302,plain,
    ( spl206_465
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10162,f8752,f29229])).

fof(f29229,plain,
    ( spl206_465
  <=> k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK80(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_465])])).

fof(f10162,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3422,f3424,f8754,f3457])).

fof(f29301,plain,
    ( spl206_464
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10163,f8752,f29224])).

fof(f29224,plain,
    ( spl206_464
  <=> k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK80(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_464])])).

fof(f10163,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3422,f3424,f8754,f3457])).

fof(f29300,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10168,f8752,f29282])).

fof(f10168,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3831,f3389,f8754,f3457])).

fof(f29299,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10176,f8752,f29073])).

fof(f10176,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3389,f8754,f3457])).

fof(f29298,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10183,f8752,f29276])).

fof(f10183,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3389,f8754,f3457])).

fof(f29297,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10184,f8752,f29271])).

fof(f10184,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3389,f8754,f3457])).

fof(f29296,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10185,f8752,f29266])).

fof(f10185,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3389,f8754,f3457])).

fof(f29295,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10190,f8752,f29282])).

fof(f10190,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3827,f3389,f8754,f3457])).

fof(f29294,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10198,f8752,f29073])).

fof(f10198,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3389,f8754,f3457])).

fof(f29293,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10205,f8752,f29276])).

fof(f10205,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3389,f8754,f3457])).

fof(f29292,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10206,f8752,f29271])).

fof(f10206,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3389,f8754,f3457])).

fof(f29291,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10207,f8752,f29266])).

fof(f10207,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3389,f8754,f3457])).

fof(f29290,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10212,f8752,f29282])).

fof(f10212,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3825,f3389,f8754,f3457])).

fof(f29289,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10220,f8752,f29073])).

% (25609)Time limit reached!
% (25609)------------------------------
% (25609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25609)Termination reason: Time limit

% (25609)Memory used [KB]: 18805
% (25609)Time elapsed: 1.305 s
% (25609)------------------------------
% (25609)------------------------------
fof(f10220,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3389,f8754,f3457])).

fof(f29288,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10227,f8752,f29276])).

fof(f10227,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3389,f8754,f3457])).

fof(f29287,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10228,f8752,f29271])).

fof(f10228,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3389,f8754,f3457])).

fof(f29286,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10229,f8752,f29266])).

fof(f10229,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3389,f8754,f3457])).

fof(f29285,plain,
    ( spl206_475
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10234,f8752,f29282])).

fof(f10234,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3822,f3389,f8754,f3457])).

fof(f29280,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10242,f8752,f29073])).

fof(f10242,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3389,f8754,f3457])).

fof(f29279,plain,
    ( spl206_474
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10249,f8752,f29276])).

fof(f10249,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3389,f8754,f3457])).

fof(f29274,plain,
    ( spl206_473
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10250,f8752,f29271])).

fof(f10250,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3389,f8754,f3457])).

fof(f29269,plain,
    ( spl206_472
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10251,f8752,f29266])).

fof(f10251,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3389,f8754,f3457])).

fof(f29264,plain,
    ( spl206_471
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10278,f8752,f29261])).

fof(f10278,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3418,f3420,f8754,f3457])).

fof(f29259,plain,
    ( spl206_458
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10286,f8752,f29021])).

fof(f10286,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3418,f3420,f8754,f3457])).

fof(f29258,plain,
    ( spl206_470
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10293,f8752,f29255])).

fof(f10293,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3418,f3420,f8754,f3457])).

fof(f29253,plain,
    ( spl206_469
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10294,f8752,f29250])).

fof(f10294,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3418,f3420,f8754,f3457])).

fof(f29248,plain,
    ( spl206_468
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10295,f8752,f29245])).

fof(f10295,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3418,f3420,f8754,f3457])).

fof(f29243,plain,
    ( spl206_467
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10300,f8752,f29240])).

fof(f10300,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k1_relat_1(k5_relat_1(k1_xboole_0,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3422,f3424,f8754,f3457])).

fof(f29238,plain,
    ( spl206_453
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10308,f8752,f28984])).

fof(f10308,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3422,f3424,f8754,f3457])).

fof(f29237,plain,
    ( spl206_466
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10315,f8752,f29234])).

fof(f10315,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k1_relat_1(k5_relat_1(sK89,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3422,f3424,f8754,f3457])).

fof(f29232,plain,
    ( spl206_465
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10316,f8752,f29229])).

fof(f10316,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k1_relat_1(k5_relat_1(sK128,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3422,f3424,f8754,f3457])).

fof(f29227,plain,
    ( spl206_464
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10317,f8752,f29224])).

fof(f10317,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k1_relat_1(k5_relat_1(sK162,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3422,f3424,f8754,f3457])).

fof(f29221,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10330,f8752,f29073])).

fof(f10330,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3389,f8754,f3457])).

fof(f29211,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10337,f8752,f29059])).

fof(f29059,plain,
    ( spl206_462
  <=> k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_462])])).

fof(f10337,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3389,f8754,f3457])).

fof(f29210,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10338,f8752,f29054])).

fof(f29054,plain,
    ( spl206_461
  <=> k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_461])])).

fof(f10338,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3389,f8754,f3457])).

fof(f29209,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10339,f8752,f29049])).

fof(f29049,plain,
    ( spl206_460
  <=> k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_460])])).

fof(f10339,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3389,f8754,f3457])).

fof(f29207,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10352,f8752,f29073])).

fof(f10352,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3389,f8754,f3457])).

fof(f29197,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10359,f8752,f29059])).

fof(f10359,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3389,f8754,f3457])).

fof(f29196,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10360,f8752,f29054])).

fof(f10360,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3389,f8754,f3457])).

fof(f29195,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10361,f8752,f29049])).

fof(f10361,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3389,f8754,f3457])).

fof(f29193,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10374,f8752,f29073])).

fof(f10374,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3389,f8754,f3457])).

fof(f29183,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10381,f8752,f29059])).

fof(f10381,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3389,f8754,f3457])).

fof(f29182,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10382,f8752,f29054])).

fof(f10382,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3389,f8754,f3457])).

fof(f29181,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10383,f8752,f29049])).

fof(f10383,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3389,f8754,f3457])).

fof(f29179,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10396,f8752,f29073])).

fof(f10396,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3389,f8754,f3457])).

fof(f29169,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10403,f8752,f29059])).

fof(f10403,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3389,f8754,f3457])).

fof(f29168,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10404,f8752,f29054])).

fof(f10404,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3389,f8754,f3457])).

fof(f29167,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10405,f8752,f29049])).

fof(f10405,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3389,f8754,f3457])).

fof(f29153,plain,
    ( spl206_459
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29152,f8752,f29031])).

fof(f29031,plain,
    ( spl206_459
  <=> k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_459])])).

fof(f29152,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f10432,f3391])).

fof(f10432,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3418,f3420,f8754,f3457])).

fof(f29147,plain,
    ( spl206_458
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10440,f8752,f29021])).

fof(f10440,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3418,f3420,f8754,f3457])).

fof(f29139,plain,
    ( spl206_457
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10447,f8752,f29009])).

fof(f29009,plain,
    ( spl206_457
  <=> k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_457])])).

fof(f10447,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3418,f3420,f8754,f3457])).

fof(f29138,plain,
    ( spl206_456
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10448,f8752,f29004])).

fof(f29004,plain,
    ( spl206_456
  <=> k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_456])])).

fof(f10448,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3418,f3420,f8754,f3457])).

fof(f29137,plain,
    ( spl206_455
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10449,f8752,f28999])).

fof(f28999,plain,
    ( spl206_455
  <=> k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_455])])).

fof(f10449,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3418,f3420,f8754,f3457])).

fof(f29136,plain,
    ( spl206_454
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29135,f8752,f28994])).

fof(f28994,plain,
    ( spl206_454
  <=> k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_454])])).

fof(f29135,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f10454,f3391])).

fof(f10454,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3422,f3424,f8754,f3457])).

fof(f29130,plain,
    ( spl206_453
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10462,f8752,f28984])).

fof(f10462,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3422,f3424,f8754,f3457])).

fof(f29122,plain,
    ( spl206_452
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10469,f8752,f28972])).

fof(f28972,plain,
    ( spl206_452
  <=> k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_452])])).

fof(f10469,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3422,f3424,f8754,f3457])).

fof(f29121,plain,
    ( spl206_451
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10470,f8752,f28967])).

fof(f28967,plain,
    ( spl206_451
  <=> k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_451])])).

fof(f10470,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3422,f3424,f8754,f3457])).

fof(f29120,plain,
    ( spl206_450
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10471,f8752,f28962])).

fof(f28962,plain,
    ( spl206_450
  <=> k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_450])])).

fof(f10471,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3422,f3424,f8754,f3457])).

fof(f29118,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10484,f8752,f29073])).

fof(f10484,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3831,f3389,f8754,f3457])).

fof(f29108,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10491,f8752,f29059])).

fof(f10491,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3831,f3389,f8754,f3457])).

fof(f29107,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10492,f8752,f29054])).

fof(f10492,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3831,f3389,f8754,f3457])).

fof(f29106,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10493,f8752,f29049])).

fof(f10493,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3831,f3389,f8754,f3457])).

fof(f29104,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10506,f8752,f29073])).

fof(f10506,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3827,f3389,f8754,f3457])).

fof(f29094,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10513,f8752,f29059])).

fof(f10513,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3827,f3389,f8754,f3457])).

fof(f29093,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10514,f8752,f29054])).

fof(f10514,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3827,f3389,f8754,f3457])).

fof(f29092,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10515,f8752,f29049])).

fof(f10515,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3827,f3389,f8754,f3457])).

fof(f29090,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10528,f8752,f29073])).

fof(f10528,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3825,f3389,f8754,f3457])).

fof(f29080,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10535,f8752,f29059])).

fof(f10535,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3825,f3389,f8754,f3457])).

fof(f29079,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10536,f8752,f29054])).

fof(f10536,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3825,f3389,f8754,f3457])).

fof(f29078,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10537,f8752,f29049])).

fof(f10537,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3825,f3389,f8754,f3457])).

fof(f29076,plain,
    ( spl206_463
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10550,f8752,f29073])).

fof(f10550,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3822,f3389,f8754,f3457])).

fof(f29062,plain,
    ( spl206_462
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10557,f8752,f29059])).

fof(f10557,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3822,f3389,f8754,f3457])).

fof(f29057,plain,
    ( spl206_461
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10558,f8752,f29054])).

fof(f10558,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3822,f3389,f8754,f3457])).

fof(f29052,plain,
    ( spl206_460
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10559,f8752,f29049])).

fof(f10559,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,k6_relat_1(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3822,f3389,f8754,f3457])).

fof(f29034,plain,
    ( spl206_459
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f29029,f8752,f29031])).

fof(f29029,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f10586,f3391])).

fof(f10586,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3418,f3420,f8754,f3457])).

fof(f29024,plain,
    ( spl206_458
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10594,f8752,f29021])).

fof(f10594,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3418,f3420,f8754,f3457])).

fof(f29012,plain,
    ( spl206_457
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10601,f8752,f29009])).

fof(f10601,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3418,f3420,f8754,f3457])).

fof(f29007,plain,
    ( spl206_456
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10602,f8752,f29004])).

fof(f10602,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3418,f3420,f8754,f3457])).

fof(f29002,plain,
    ( spl206_455
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10603,f8752,f28999])).

fof(f10603,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK79(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3418,f3420,f8754,f3457])).

fof(f28997,plain,
    ( spl206_454
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f28992,f8752,f28994])).

fof(f28992,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f10608,f3391])).

fof(f10608,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3422,f3424,f8754,f3457])).

fof(f28987,plain,
    ( spl206_453
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10616,f8752,f28984])).

fof(f10616,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3422,f3424,f8754,f3457])).

fof(f28975,plain,
    ( spl206_452
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10623,f8752,f28972])).

fof(f10623,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3422,f3424,f8754,f3457])).

fof(f28970,plain,
    ( spl206_451
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10624,f8752,f28967])).

fof(f10624,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3422,f3424,f8754,f3457])).

fof(f28965,plain,
    ( spl206_450
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10625,f8752,f28962])).

fof(f10625,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k1_relat_1(k5_relat_1(sK3,sK80(k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3422,f3424,f8754,f3457])).

fof(f28960,plain,
    ( spl206_449
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10630,f8752,f28957])).

fof(f28957,plain,
    ( spl206_449
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_449])])).

fof(f10630,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,k1_xboole_0)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3460])).

fof(f3460,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f1745,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f843])).

fof(f843,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f28955,plain,
    ( spl206_444
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10638,f8752,f28926])).

fof(f28926,plain,
    ( spl206_444
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK3)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_444])])).

fof(f10638,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK3)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3460])).

fof(f28954,plain,
    ( spl206_448
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10645,f8752,f28951])).

fof(f28951,plain,
    ( spl206_448
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK89)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_448])])).

fof(f10645,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK89)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3460])).

fof(f28949,plain,
    ( spl206_447
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10646,f8752,f28946])).

fof(f28946,plain,
    ( spl206_447
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK128)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_447])])).

fof(f10646,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK128)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3460])).

fof(f28944,plain,
    ( spl206_446
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10647,f8752,f28941])).

fof(f28941,plain,
    ( spl206_446
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK3,sK162)),k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_446])])).

fof(f10647,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK162)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3460])).

fof(f28939,plain,
    ( spl206_445
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f28934,f8752,f28936])).

fof(f28936,plain,
    ( spl206_445
  <=> r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_445])])).

fof(f28934,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k1_xboole_0)
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f10652,f3391])).

fof(f10652,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(k1_xboole_0,sK3)),k1_relat_1(k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3460])).

fof(f28929,plain,
    ( spl206_444
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10660,f8752,f28926])).

fof(f10660,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK3)),k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3460])).

fof(f28916,plain,
    ( spl206_443
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10667,f8752,f28913])).

fof(f28913,plain,
    ( spl206_443
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK89,sK3)),k1_relat_1(sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_443])])).

fof(f10667,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK89,sK3)),k1_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3460])).

fof(f28911,plain,
    ( spl206_442
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10668,f8752,f28908])).

fof(f28908,plain,
    ( spl206_442
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK128,sK3)),k1_relat_1(sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_442])])).

fof(f10668,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK128,sK3)),k1_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3460])).

fof(f28906,plain,
    ( spl206_441
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10669,f8752,f28903])).

fof(f28903,plain,
    ( spl206_441
  <=> r1_tarski(k1_relat_1(k5_relat_1(sK162,sK3)),k1_relat_1(sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_441])])).

fof(f10669,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK162,sK3)),k1_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3460])).

fof(f28901,plain,
    ( spl206_440
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10674,f8752,f28898])).

fof(f28898,plain,
    ( spl206_440
  <=> k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_440])])).

fof(f10674,plain,
    ( k1_xboole_0 = k5_relat_1(k1_xboole_0,sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3481])).

fof(f3481,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1757])).

fof(f1757,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f857])).

fof(f857,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
        & k1_xboole_0 = k5_relat_1(k1_xboole_0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_relat_1)).

fof(f28896,plain,
    ( spl206_439
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10675,f8752,f28893])).

fof(f28893,plain,
    ( spl206_439
  <=> k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_439])])).

fof(f10675,plain,
    ( k1_xboole_0 = k5_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3482])).

fof(f3482,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1757])).

fof(f28891,plain,
    ( spl206_438
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10676,f8752,f28888])).

fof(f10676,plain,
    ( k1_xboole_0 = k9_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3483])).

fof(f3483,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1758])).

fof(f1758,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f751])).

fof(f751,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f28886,plain,
    ( ~ spl206_437
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10685,f8752,f28883])).

fof(f28883,plain,
    ( spl206_437
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_437])])).

fof(f10685,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4300,f4298,f4021,f8754,f3512])).

fof(f3512,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK99(X0,X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2464])).

fof(f2464,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK99(X0,X1))
            | ~ r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK99(X0,X1)) ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK99])],[f2462,f2463])).

fof(f2463,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK99(X0,X1))
            | ~ r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK99(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2462,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2461])).

fof(f2461,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ~ r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f1770])).

fof(f1770,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1769])).

fof(f1769,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1154])).

fof(f1154,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1)
        & v1_relat_1(X0) )
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(k4_tarski(X3,k1_funct_1(X1,X3)),X0)
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e4_51__wellord1)).

fof(f4300,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1114])).

fof(f28881,plain,
    ( ~ spl206_436
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10698,f8752,f28878])).

fof(f28878,plain,
    ( spl206_436
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_436])])).

fof(f10698,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3463,f3462,f4021,f8754,f3512])).

fof(f28876,plain,
    ( ~ spl206_435
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10699,f8752,f28873])).

fof(f28873,plain,
    ( spl206_435
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_435])])).

fof(f10699,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK99(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3901,f3900,f4021,f8754,f3512])).

fof(f28871,plain,
    ( spl206_434
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10705,f8752,f28868])).

fof(f28868,plain,
    ( spl206_434
  <=> v1_xboole_0(k8_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_434])])).

fof(f10705,plain,
    ( v1_xboole_0(k8_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3580])).

fof(f3580,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f1795,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1794])).

fof(f1794,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) )
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f687])).

fof(f687,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & v1_relat_1(X0) )
     => ( v1_relat_1(k8_relat_1(X1,X0))
        & v1_xboole_0(k8_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc18_relat_1)).

fof(f28866,plain,
    ( spl206_433
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10706,f8752,f28863])).

fof(f28863,plain,
    ( spl206_433
  <=> v1_xboole_0(k8_relat_1(sK129,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_433])])).

fof(f10706,plain,
    ( v1_xboole_0(k8_relat_1(sK129,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3580])).

fof(f28861,plain,
    ( spl206_432
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10708,f8752,f28858])).

fof(f28858,plain,
    ( spl206_432
  <=> v1_relat_1(k8_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_432])])).

fof(f10708,plain,
    ( v1_relat_1(k8_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3581])).

fof(f3581,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X1,X0))
      | ~ v1_xboole_0(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1795])).

fof(f28856,plain,
    ( spl206_431
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10709,f8752,f28853])).

fof(f28853,plain,
    ( spl206_431
  <=> v1_relat_1(k8_relat_1(sK129,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_431])])).

fof(f10709,plain,
    ( v1_relat_1(k8_relat_1(sK129,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3581])).

fof(f28851,plain,
    ( spl206_430
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10711,f8752,f28848])).

fof(f28848,plain,
    ( spl206_430
  <=> v1_xboole_0(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_430])])).

fof(f10711,plain,
    ( v1_xboole_0(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3582])).

fof(f3582,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1797])).

fof(f1797,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1796])).

fof(f1796,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f683])).

fof(f683,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X1,X0))
        & v1_xboole_0(k5_relat_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_relat_1)).

fof(f28846,plain,
    ( spl206_429
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10712,f8752,f28843])).

fof(f28843,plain,
    ( spl206_429
  <=> v1_xboole_0(k5_relat_1(sK3,sK129)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_429])])).

fof(f10712,plain,
    ( v1_xboole_0(k5_relat_1(sK3,sK129))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3582])).

fof(f28841,plain,
    ( spl206_221
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10714,f8752,f24150])).

fof(f10714,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3583])).

fof(f3583,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1797])).

fof(f28840,plain,
    ( spl206_428
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10715,f8752,f28837])).

fof(f28837,plain,
    ( spl206_428
  <=> v1_relat_1(k5_relat_1(sK3,sK129)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_428])])).

fof(f10715,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK129))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3583])).

fof(f28835,plain,
    ( spl206_427
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10717,f8752,f28832])).

fof(f28832,plain,
    ( spl206_427
  <=> v1_xboole_0(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_427])])).

fof(f10717,plain,
    ( v1_xboole_0(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3584])).

fof(f3584,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f1799,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f1798])).

fof(f1798,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) )
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f682])).

fof(f682,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k5_relat_1(X0,X1))
        & v1_xboole_0(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc12_relat_1)).

fof(f28830,plain,
    ( spl206_426
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10718,f8752,f28827])).

fof(f28827,plain,
    ( spl206_426
  <=> v1_xboole_0(k5_relat_1(sK129,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_426])])).

fof(f10718,plain,
    ( v1_xboole_0(k5_relat_1(sK129,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3584])).

fof(f28825,plain,
    ( spl206_218
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10720,f8752,f24133])).

fof(f10720,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3492,f8754,f3585])).

fof(f3585,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1799])).

fof(f28824,plain,
    ( spl206_425
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10721,f8752,f28821])).

fof(f28821,plain,
    ( spl206_425
  <=> v1_relat_1(k5_relat_1(sK129,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_425])])).

fof(f10721,plain,
    ( v1_relat_1(k5_relat_1(sK129,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3573,f8754,f3585])).

fof(f28819,plain,
    ( spl206_424
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10727,f8752,f28816])).

fof(f28816,plain,
    ( spl206_424
  <=> k1_xboole_0 = k1_wellord1(sK3,sK177(k3_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_424])])).

fof(f10727,plain,
    ( k1_xboole_0 = k1_wellord1(sK3,sK177(k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4021,f8754,f3754])).

fof(f3754,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_wellord1(X1,X0)
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1870])).

fof(f1870,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_wellord1(X1,X0)
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1869])).

fof(f1869,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k1_wellord1(X1,X0)
      | r2_hidden(X0,k3_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1174])).

fof(f1174,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

fof(f28813,plain,
    ( spl206_423
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10736,f8752,f28810])).

fof(f28810,plain,
    ( spl206_423
  <=> sK3 = k2_wellord1(sK3,k3_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_423])])).

fof(f10736,plain,
    ( sK3 = k2_wellord1(sK3,k3_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3763])).

fof(f3763,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1878])).

fof(f1878,plain,(
    ! [X0] :
      ( k2_wellord1(X0,k3_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1175])).

fof(f1175,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_wellord1(X0,k3_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

fof(f28808,plain,
    ( spl206_422
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10737,f8752,f28805])).

fof(f28805,plain,
    ( spl206_422
  <=> k3_relat_1(sK3) = k3_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_422])])).

fof(f10737,plain,
    ( k3_relat_1(sK3) = k3_relat_1(k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3764])).

fof(f3764,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1879])).

fof(f1879,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f839])).

fof(f839,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k3_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relat_1)).

fof(f28801,plain,
    ( spl206_419
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10780,f8752,f5107,f28728])).

fof(f28728,plain,
    ( spl206_419
  <=> r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_419])])).

fof(f10780,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3773])).

fof(f3773,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1889])).

fof(f1889,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1888])).

fof(f1888,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f736])).

fof(f736,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X3)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

fof(f28798,plain,
    ( spl206_419
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10823,f8752,f5107,f28728])).

fof(f10823,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3773])).

fof(f28795,plain,
    ( spl206_419
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10866,f8752,f5107,f28728])).

fof(f10866,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3773])).

fof(f28792,plain,
    ( spl206_419
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10909,f8752,f5107,f28728])).

fof(f10909,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3773])).

fof(f28745,plain,
    ( spl206_421
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f10995,f8752,f5107,f28742])).

fof(f28742,plain,
    ( spl206_421
  <=> k8_relat_1(sK1,sK3) = k8_relat_1(sK1,k8_relat_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_421])])).

fof(f10995,plain,
    ( k8_relat_1(sK1,sK3) = k8_relat_1(sK1,k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3774])).

fof(f3774,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1891])).

fof(f1891,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1890])).

fof(f1890,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f733])).

fof(f733,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_relat_1)).

fof(f28738,plain,
    ( spl206_420
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11038,f8752,f5107,f28735])).

fof(f28735,plain,
    ( spl206_420
  <=> k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_420])])).

fof(f11038,plain,
    ( k8_relat_1(sK1,sK3) = k8_relat_1(sK2,k8_relat_1(sK1,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3775])).

fof(f3775,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1893])).

fof(f1893,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1892])).

fof(f1892,plain,(
    ! [X0,X1,X2] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f732])).

fof(f732,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

fof(f28731,plain,
    ( spl206_419
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11081,f8752,f5107,f28728])).

fof(f11081,plain,
    ( r1_tarski(k8_relat_1(sK1,sK3),k8_relat_1(sK2,sK3))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3776])).

fof(f3776,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1895])).

fof(f1895,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1894])).

fof(f1894,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f734])).

fof(f734,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k8_relat_1(X0,X2),k8_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t131_relat_1)).

fof(f28721,plain,
    ( spl206_418
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11225,f8752,f28718])).

fof(f28718,plain,
    ( spl206_418
  <=> k1_xboole_0 = k8_relat_1(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_418])])).

fof(f11225,plain,
    ( k1_xboole_0 = k8_relat_1(k1_xboole_0,sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3802])).

fof(f3802,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1916])).

fof(f1916,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f740])).

fof(f740,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_relat_1)).

fof(f28716,plain,
    ( spl206_416
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11226,f8752,f28706])).

fof(f28706,plain,
    ( spl206_416
  <=> sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_416])])).

fof(f11226,plain,
    ( sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3813])).

fof(f3813,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1924])).

fof(f1924,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1923])).

fof(f1923,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f869])).

fof(f869,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f28715,plain,
    ( spl206_416
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11227,f8752,f28706])).

fof(f11227,plain,
    ( sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3813])).

fof(f28714,plain,
    ( spl206_417
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11228,f8752,f28711])).

fof(f28711,plain,
    ( spl206_417
  <=> sK3 = k5_relat_1(k6_relat_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_417])])).

fof(f11228,plain,
    ( sK3 = k5_relat_1(k6_relat_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f3813])).

fof(f28709,plain,
    ( spl206_416
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11232,f8752,f28706])).

fof(f11232,plain,
    ( sK3 = k5_relat_1(k6_relat_1(k1_relat_1(sK3)),sK3)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3821])).

fof(f3821,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1934])).

fof(f1934,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f870])).

fof(f870,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f28702,plain,
    ( spl206_415
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11275,f8752,f5107,f28643])).

fof(f28643,plain,
    ( spl206_415
  <=> r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_415])])).

fof(f11275,plain,
    ( r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3871])).

fof(f3871,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1956])).

fof(f1956,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1955])).

fof(f1955,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f782])).

fof(f782,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t180_relat_1)).

fof(f28699,plain,
    ( spl206_415
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11318,f8752,f5107,f28643])).

fof(f11318,plain,
    ( r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3871])).

fof(f28696,plain,
    ( spl206_415
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11361,f8752,f5107,f28643])).

fof(f11361,plain,
    ( r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3871])).

fof(f28693,plain,
    ( spl206_415
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11404,f8752,f5107,f28643])).

fof(f11404,plain,
    ( r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3871])).

fof(f28646,plain,
    ( spl206_415
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11490,f8752,f5107,f28643])).

fof(f11490,plain,
    ( r1_tarski(k10_relat_1(sK3,sK1),k10_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3872])).

fof(f3872,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1958])).

fof(f1958,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1957])).

fof(f1957,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f780])).

fof(f780,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

fof(f28636,plain,
    ( spl206_414
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11541,f8752,f28632])).

fof(f28632,plain,
    ( spl206_414
  <=> r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,k9_relat_1(sK3,k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_414])])).

fof(f11541,plain,
    ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,k9_relat_1(sK3,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f3882])).

fof(f3882,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1975])).

fof(f1975,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f1974])).

fof(f1974,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0)))
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f965])).

fof(f965,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => r1_tarski(X0,k10_relat_1(X1,k9_relat_1(X1,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

fof(f28635,plain,
    ( spl206_414
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11542,f8752,f28632])).

fof(f11542,plain,
    ( r1_tarski(k1_relat_1(sK3),k10_relat_1(sK3,k9_relat_1(sK3,k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f3882])).

fof(f28630,plain,
    ( spl206_413
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11546,f8752,f28627])).

fof(f28627,plain,
    ( spl206_413
  <=> r1_tarski(k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)),k10_relat_1(sK3,k9_relat_1(sK3,k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_413])])).

fof(f11546,plain,
    ( r1_tarski(k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)),k10_relat_1(sK3,k9_relat_1(sK3,k2_relat_1(sK6(k1_relat_1(sK3),k1_xboole_0)))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4871,f8754,f3882])).

fof(f28625,plain,
    ( spl206_412
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f28620,f8752,f28622])).

fof(f28622,plain,
    ( spl206_412
  <=> k10_relat_1(sK3,k1_xboole_0) = k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_412])])).

fof(f28620,plain,
    ( k10_relat_1(sK3,k1_xboole_0) = k1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f11550,f3391])).

fof(f11550,plain,
    ( k1_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k10_relat_1(sK3,k1_relat_1(k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3888])).

fof(f3888,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1982])).

fof(f1982,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f784])).

fof(f784,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f28615,plain,
    ( spl206_407
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11558,f8752,f28582])).

fof(f28582,plain,
    ( spl206_407
  <=> k1_relat_1(k5_relat_1(sK3,sK3)) = k10_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_407])])).

fof(f11558,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k10_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3888])).

fof(f28606,plain,
    ( spl206_411
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11565,f8752,f28603])).

fof(f28603,plain,
    ( spl206_411
  <=> k1_relat_1(k5_relat_1(sK3,sK89)) = k10_relat_1(sK3,k1_relat_1(sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_411])])).

fof(f11565,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK89)) = k10_relat_1(sK3,k1_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3888])).

fof(f28601,plain,
    ( spl206_410
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11566,f8752,f28598])).

fof(f28598,plain,
    ( spl206_410
  <=> k1_relat_1(k5_relat_1(sK3,sK128)) = k10_relat_1(sK3,k1_relat_1(sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_410])])).

fof(f11566,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK128)) = k10_relat_1(sK3,k1_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3888])).

fof(f28596,plain,
    ( spl206_409
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11567,f8752,f28593])).

fof(f28593,plain,
    ( spl206_409
  <=> k1_relat_1(k5_relat_1(sK3,sK162)) = k10_relat_1(sK3,k1_relat_1(sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_409])])).

fof(f11567,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK162)) = k10_relat_1(sK3,k1_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3888])).

fof(f28591,plain,
    ( spl206_408
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f28586,f8752,f28588])).

fof(f28588,plain,
    ( spl206_408
  <=> k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_408])])).

fof(f28586,plain,
    ( k1_xboole_0 = k1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f11572,f3890])).

fof(f3890,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f774])).

fof(f774,axiom,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

fof(f11572,plain,
    ( k1_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k10_relat_1(k1_xboole_0,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3888])).

fof(f28585,plain,
    ( spl206_407
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11580,f8752,f28582])).

fof(f11580,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK3)) = k10_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3888])).

fof(f28580,plain,
    ( spl206_406
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11587,f8752,f28577])).

fof(f28577,plain,
    ( spl206_406
  <=> k1_relat_1(k5_relat_1(sK89,sK3)) = k10_relat_1(sK89,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_406])])).

fof(f11587,plain,
    ( k1_relat_1(k5_relat_1(sK89,sK3)) = k10_relat_1(sK89,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3888])).

fof(f28575,plain,
    ( spl206_405
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11588,f8752,f28572])).

fof(f28572,plain,
    ( spl206_405
  <=> k1_relat_1(k5_relat_1(sK128,sK3)) = k10_relat_1(sK128,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_405])])).

fof(f11588,plain,
    ( k1_relat_1(k5_relat_1(sK128,sK3)) = k10_relat_1(sK128,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3888])).

fof(f28570,plain,
    ( spl206_404
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11589,f8752,f28567])).

fof(f28567,plain,
    ( spl206_404
  <=> k1_relat_1(k5_relat_1(sK162,sK3)) = k10_relat_1(sK162,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_404])])).

fof(f11589,plain,
    ( k1_relat_1(k5_relat_1(sK162,sK3)) = k10_relat_1(sK162,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3888])).

fof(f28565,plain,
    ( spl206_403
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11594,f8752,f28562])).

fof(f11594,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,k1_xboole_0)
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3889])).

fof(f3889,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1983])).

fof(f1983,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f773])).

fof(f773,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f28558,plain,
    ( spl206_402
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11637,f8752,f5107,f28499])).

fof(f28499,plain,
    ( spl206_402
  <=> r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_402])])).

fof(f11637,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3893])).

fof(f3893,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1989])).

fof(f1989,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1988])).

fof(f1988,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1))
          | ~ r1_tarski(X0,X1)
          | ~ r1_tarski(X2,X3)
          | ~ v1_relat_1(X3) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f761])).

fof(f761,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ! [X3] :
          ( v1_relat_1(X3)
         => ( ( r1_tarski(X0,X1)
              & r1_tarski(X2,X3) )
           => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X3,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_relat_1)).

fof(f28555,plain,
    ( spl206_402
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11680,f8752,f5107,f28499])).

fof(f11680,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3893])).

fof(f28552,plain,
    ( spl206_402
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11723,f8752,f5107,f28499])).

fof(f11723,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4882,f8754,f3893])).

fof(f28549,plain,
    ( spl206_402
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11766,f8752,f5107,f28499])).

fof(f11766,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4881,f8754,f3893])).

fof(f28502,plain,
    ( spl206_402
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11852,f8752,f5107,f28499])).

fof(f11852,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),k9_relat_1(sK3,sK2))
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3894])).

fof(f3894,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1991])).

fof(f1991,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1990])).

fof(f1990,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f759])).

fof(f759,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t156_relat_1)).

fof(f28492,plain,
    ( spl206_221
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11903,f8752,f24150])).

fof(f11903,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3921])).

fof(f3921,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2023])).

fof(f2023,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2022])).

fof(f2022,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f667])).

fof(f667,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f28491,plain,
    ( spl206_398
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11911,f8752,f28471])).

fof(f11911,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3921])).

fof(f28490,plain,
    ( spl206_401
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11918,f8752,f28487])).

fof(f11918,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3921])).

fof(f28485,plain,
    ( spl206_400
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11919,f8752,f28482])).

fof(f11919,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3921])).

fof(f28480,plain,
    ( spl206_399
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11920,f8752,f28477])).

fof(f11920,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3921])).

fof(f28475,plain,
    ( spl206_218
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11925,f8752,f24133])).

fof(f11925,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f3921])).

fof(f28474,plain,
    ( spl206_398
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11933,f8752,f28471])).

fof(f11933,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f3921])).

fof(f28469,plain,
    ( spl206_397
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11940,f8752,f28466])).

fof(f11940,plain,
    ( v1_relat_1(k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f3921])).

fof(f28464,plain,
    ( spl206_396
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11941,f8752,f28461])).

fof(f11941,plain,
    ( v1_relat_1(k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f3921])).

fof(f28459,plain,
    ( spl206_395
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11942,f8752,f28456])).

fof(f11942,plain,
    ( v1_relat_1(k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f3921])).

fof(f28454,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11955,f8752,f28340])).

fof(f28340,plain,
    ( spl206_383
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_383])])).

fof(f11955,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f3922,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X3)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2025])).

fof(f2025,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2024])).

fof(f2024,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3))
                  | ~ r1_tarski(X2,X3)
                  | ~ r1_tarski(X0,X1)
                  | ~ v1_relat_1(X3) )
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f849])).

fof(f849,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ! [X3] :
                  ( v1_relat_1(X3)
                 => ( ( r1_tarski(X2,X3)
                      & r1_tarski(X0,X1) )
                   => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X3)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_relat_1)).

fof(f28453,plain,
    ( spl206_382
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11962,f8752,f28335])).

fof(f28335,plain,
    ( spl206_382
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_382])])).

fof(f11962,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28452,plain,
    ( spl206_381
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11963,f8752,f28330])).

fof(f28330,plain,
    ( spl206_381
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_381])])).

fof(f11963,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28451,plain,
    ( spl206_380
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f11964,f8752,f28325])).

fof(f28325,plain,
    ( spl206_380
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_380])])).

fof(f11964,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28450,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12097,f8752,f28340])).

fof(f12097,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28449,plain,
    ( spl206_382
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12104,f8752,f28335])).

fof(f12104,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28448,plain,
    ( spl206_381
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12105,f8752,f28330])).

fof(f12105,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28447,plain,
    ( spl206_380
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12106,f8752,f28325])).

fof(f12106,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28446,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12239,f8752,f28340])).

fof(f12239,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28445,plain,
    ( spl206_382
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12246,f8752,f28335])).

fof(f12246,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28444,plain,
    ( spl206_381
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12247,f8752,f28330])).

fof(f12247,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28443,plain,
    ( spl206_380
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12248,f8752,f28325])).

fof(f12248,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f2830,f4298,f8754,f4882,f8754,f3922])).

fof(f28442,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12381,f8752,f28340])).

fof(f12381,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28441,plain,
    ( spl206_382
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12388,f8752,f28335])).

fof(f12388,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28440,plain,
    ( spl206_381
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12389,f8752,f28330])).

fof(f12389,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28439,plain,
    ( spl206_380
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12390,f8752,f28325])).

fof(f12390,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f2830,f4298,f8754,f4881,f8754,f3922])).

fof(f28438,plain,
    ( spl206_379
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12515,f8752,f28320])).

fof(f28320,plain,
    ( spl206_379
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_379])])).

fof(f12515,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f2830,f4298,f4298,f2830,f8754,f3922])).

fof(f28437,plain,
    ( spl206_391
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12523,f8752,f28381])).

fof(f28381,plain,
    ( spl206_391
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_391])])).

fof(f12523,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f2830,f4298,f4298,f2830,f8754,f3922])).

fof(f28436,plain,
    ( spl206_394
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12530,f8752,f28433])).

fof(f28433,plain,
    ( spl206_394
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_394])])).

fof(f12530,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f2830,f4298,f4298,f2830,f8754,f3922])).

fof(f28431,plain,
    ( spl206_393
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12531,f8752,f28428])).

fof(f28428,plain,
    ( spl206_393
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_393])])).

fof(f12531,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f2830,f4298,f4298,f2830,f8754,f3922])).

fof(f28426,plain,
    ( spl206_392
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12532,f8752,f28423])).

fof(f28423,plain,
    ( spl206_392
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_392])])).

fof(f12532,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f2830,f4298,f4298,f2830,f8754,f3922])).

fof(f28421,plain,
    ( spl206_379
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12537,f8752,f28320])).

fof(f12537,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4882,f4298,f4298,f2830,f8754,f3922])).

fof(f28420,plain,
    ( spl206_379
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12538,f8752,f28320])).

fof(f12538,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4881,f4298,f4298,f2830,f8754,f3922])).

fof(f28419,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12629,f8752,f28299])).

fof(f28299,plain,
    ( spl206_375
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_375])])).

fof(f12629,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4882,f8754,f4298,f2830,f8754,f3922])).

fof(f28418,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12630,f8752,f28299])).

fof(f12630,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4881,f8754,f4298,f2830,f8754,f3922])).

fof(f28417,plain,
    ( spl206_378
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12643,f8752,f28314])).

fof(f28314,plain,
    ( spl206_378
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_378])])).

fof(f12643,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4882,f3462,f4298,f2830,f8754,f3922])).

fof(f28416,plain,
    ( spl206_378
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12644,f8752,f28314])).

fof(f12644,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4881,f3462,f4298,f2830,f8754,f3922])).

fof(f28415,plain,
    ( spl206_377
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12645,f8752,f28309])).

fof(f28309,plain,
    ( spl206_377
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_377])])).

fof(f12645,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4882,f3572,f4298,f2830,f8754,f3922])).

fof(f28414,plain,
    ( spl206_377
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12646,f8752,f28309])).

fof(f12646,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4881,f3572,f4298,f2830,f8754,f3922])).

fof(f28413,plain,
    ( spl206_376
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12647,f8752,f28304])).

fof(f28304,plain,
    ( spl206_376
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_376])])).

fof(f12647,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4882,f3900,f4298,f2830,f8754,f3922])).

fof(f28412,plain,
    ( spl206_376
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12648,f8752,f28304])).

fof(f12648,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4881,f3900,f4298,f2830,f8754,f3922])).

fof(f28411,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12737,f8752,f28299])).

fof(f12737,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28410,plain,
    ( spl206_374
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12744,f8752,f28294])).

fof(f28294,plain,
    ( spl206_374
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_374])])).

fof(f12744,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28409,plain,
    ( spl206_373
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12745,f8752,f28289])).

fof(f28289,plain,
    ( spl206_373
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_373])])).

fof(f12745,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28408,plain,
    ( spl206_372
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12746,f8752,f28284])).

fof(f28284,plain,
    ( spl206_372
  <=> r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_372])])).

fof(f12746,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28407,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12879,f8752,f28299])).

fof(f12879,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28406,plain,
    ( spl206_374
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12886,f8752,f28294])).

fof(f12886,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28405,plain,
    ( spl206_373
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12887,f8752,f28289])).

fof(f12887,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28404,plain,
    ( spl206_372
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f12888,f8752,f28284])).

fof(f12888,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28403,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13021,f8752,f28299])).

fof(f13021,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28402,plain,
    ( spl206_374
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13028,f8752,f28294])).

fof(f13028,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28401,plain,
    ( spl206_373
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13029,f8752,f28289])).

fof(f13029,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28400,plain,
    ( spl206_372
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13030,f8752,f28284])).

fof(f13030,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f4882,f8754,f3922])).

fof(f28399,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13163,f8752,f28299])).

fof(f13163,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28398,plain,
    ( spl206_374
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13170,f8752,f28294])).

fof(f13170,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28397,plain,
    ( spl206_373
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13171,f8752,f28289])).

fof(f13171,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28396,plain,
    ( spl206_372
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13172,f8752,f28284])).

fof(f13172,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f4881,f8754,f3922])).

fof(f28395,plain,
    ( spl206_387
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13225,f8752,f28361])).

fof(f28361,plain,
    ( spl206_387
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_387])])).

fof(f13225,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f4882,f4298,f2830,f8754,f3922])).

fof(f28394,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13247,f8752,f28340])).

fof(f13247,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4882,f4298,f2830,f8754,f3922])).

fof(f28393,plain,
    ( spl206_386
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13254,f8752,f28355])).

fof(f28355,plain,
    ( spl206_386
  <=> r1_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_386])])).

fof(f13254,plain,
    ( r1_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4882,f4298,f2830,f8754,f3922])).

fof(f28392,plain,
    ( spl206_385
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13255,f8752,f28350])).

fof(f28350,plain,
    ( spl206_385
  <=> r1_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_385])])).

fof(f13255,plain,
    ( r1_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4882,f4298,f2830,f8754,f3922])).

fof(f28391,plain,
    ( spl206_384
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13256,f8752,f28345])).

fof(f28345,plain,
    ( spl206_384
  <=> r1_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_384])])).

fof(f13256,plain,
    ( r1_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4882,f4298,f2830,f8754,f3922])).

fof(f28390,plain,
    ( spl206_387
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13261,f8752,f28361])).

fof(f13261,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f4881,f4298,f2830,f8754,f3922])).

fof(f28389,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13283,f8752,f28340])).

fof(f13283,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4881,f4298,f2830,f8754,f3922])).

fof(f28388,plain,
    ( spl206_386
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13290,f8752,f28355])).

fof(f13290,plain,
    ( r1_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4881,f4298,f2830,f8754,f3922])).

fof(f28387,plain,
    ( spl206_385
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13291,f8752,f28350])).

fof(f13291,plain,
    ( r1_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4881,f4298,f2830,f8754,f3922])).

fof(f28386,plain,
    ( spl206_384
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13292,f8752,f28345])).

fof(f13292,plain,
    ( r1_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4881,f4298,f2830,f8754,f3922])).

fof(f28385,plain,
    ( spl206_387
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13297,f8752,f28361])).

fof(f13297,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f2830,f4298,f2830,f8754,f3922])).

fof(f28384,plain,
    ( spl206_391
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13305,f8752,f28381])).

fof(f13305,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f4298,f2830,f8754,f3922])).

fof(f28379,plain,
    ( spl206_390
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13312,f8752,f28376])).

fof(f28376,plain,
    ( spl206_390
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_390])])).

fof(f13312,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f4298,f2830,f8754,f3922])).

fof(f28374,plain,
    ( spl206_389
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13313,f8752,f28371])).

fof(f28371,plain,
    ( spl206_389
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_389])])).

fof(f13313,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f4298,f2830,f8754,f3922])).

fof(f28369,plain,
    ( spl206_388
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13314,f8752,f28366])).

fof(f28366,plain,
    ( spl206_388
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_388])])).

fof(f13314,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f4298,f2830,f8754,f3922])).

fof(f28364,plain,
    ( spl206_387
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13455,f8752,f28361])).

fof(f13455,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f2830,f8754,f3923])).

fof(f3923,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2027])).

fof(f2027,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2026])).

fof(f2026,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f847])).

fof(f847,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f28359,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13463,f8752,f28340])).

fof(f13463,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f3923])).

fof(f28358,plain,
    ( spl206_386
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13470,f8752,f28355])).

fof(f13470,plain,
    ( r1_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f3923])).

fof(f28353,plain,
    ( spl206_385
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13471,f8752,f28350])).

fof(f13471,plain,
    ( r1_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f3923])).

fof(f28348,plain,
    ( spl206_384
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13472,f8752,f28345])).

fof(f13472,plain,
    ( r1_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f3923])).

fof(f28343,plain,
    ( spl206_383
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13557,f8752,f28340])).

fof(f13557,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f3923])).

fof(f28338,plain,
    ( spl206_382
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13564,f8752,f28335])).

fof(f13564,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f3923])).

fof(f28333,plain,
    ( spl206_381
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13565,f8752,f28330])).

fof(f13565,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f3923])).

fof(f28328,plain,
    ( spl206_380
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13566,f8752,f28325])).

fof(f13566,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f3923])).

fof(f28323,plain,
    ( spl206_379
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13707,f8752,f28320])).

fof(f13707,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f2830,f8754,f3924])).

fof(f3924,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2029])).

fof(f2029,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2028])).

fof(f2028,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f848])).

fof(f848,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X0,X2),k5_relat_1(X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relat_1)).

fof(f28318,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13715,f8752,f28299])).

fof(f13715,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f3924])).

fof(f28317,plain,
    ( spl206_378
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13722,f8752,f28314])).

fof(f13722,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f3924])).

fof(f28312,plain,
    ( spl206_377
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13723,f8752,f28309])).

fof(f13723,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f3924])).

fof(f28307,plain,
    ( spl206_376
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13724,f8752,f28304])).

fof(f13724,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f3924])).

fof(f28302,plain,
    ( spl206_375
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13809,f8752,f28299])).

fof(f13809,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f2830,f8754,f3924])).

fof(f28297,plain,
    ( spl206_374
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13816,f8752,f28294])).

fof(f13816,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f2830,f8754,f3924])).

fof(f28292,plain,
    ( spl206_373
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13817,f8752,f28289])).

fof(f13817,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f2830,f8754,f3924])).

fof(f28287,plain,
    ( spl206_372
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13818,f8752,f28284])).

fof(f13818,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f2830,f8754,f3924])).

fof(f28282,plain,
    ( spl206_371
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13871,f8752,f28279])).

fof(f28279,plain,
    ( spl206_371
  <=> k5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_371])])).

fof(f13871,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f3925])).

fof(f3925,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2030])).

fof(f2030,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f854])).

fof(f854,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f28277,plain,
    ( spl206_334
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13879,f8752,f28080])).

fof(f28080,plain,
    ( spl206_334
  <=> k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK3) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_334])])).

fof(f13879,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK3) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f3925])).

fof(f28276,plain,
    ( spl206_370
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13886,f8752,f28273])).

fof(f28273,plain,
    ( spl206_370
  <=> k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK89) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_370])])).

fof(f13886,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK89) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f3925])).

fof(f28271,plain,
    ( spl206_369
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13887,f8752,f28268])).

fof(f28268,plain,
    ( spl206_369
  <=> k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK128) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_369])])).

fof(f13887,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK128) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f3925])).

fof(f28266,plain,
    ( spl206_368
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f13888,f8752,f28263])).

fof(f28263,plain,
    ( spl206_368
  <=> k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK162) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_368])])).

fof(f13888,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK162) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f3925])).

fof(f28261,plain,
    ( spl206_354
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14047,f8752,f28185])).

fof(f28185,plain,
    ( spl206_354
  <=> k5_relat_1(k5_relat_1(sK3,sK3),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_354])])).

fof(f14047,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f3925])).

fof(f28260,plain,
    ( spl206_329
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14055,f8752,f28055])).

fof(f28055,plain,
    ( spl206_329
  <=> k5_relat_1(k5_relat_1(sK3,sK3),sK3) = k5_relat_1(sK3,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_329])])).

fof(f14055,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK3) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f3925])).

fof(f28259,plain,
    ( spl206_349
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14062,f8752,f28155])).

fof(f28155,plain,
    ( spl206_349
  <=> k5_relat_1(k5_relat_1(sK3,sK3),sK89) = k5_relat_1(sK3,k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_349])])).

fof(f14062,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK89) = k5_relat_1(sK3,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f3925])).

fof(f28258,plain,
    ( spl206_344
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14063,f8752,f28130])).

fof(f28130,plain,
    ( spl206_344
  <=> k5_relat_1(k5_relat_1(sK3,sK3),sK128) = k5_relat_1(sK3,k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_344])])).

fof(f14063,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK128) = k5_relat_1(sK3,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f3925])).

fof(f28257,plain,
    ( spl206_339
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14064,f8752,f28105])).

fof(f28105,plain,
    ( spl206_339
  <=> k5_relat_1(k5_relat_1(sK3,sK3),sK162) = k5_relat_1(sK3,k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_339])])).

fof(f14064,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK162) = k5_relat_1(sK3,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f3925])).

fof(f28256,plain,
    ( spl206_367
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14201,f8752,f28253])).

fof(f28253,plain,
    ( spl206_367
  <=> k5_relat_1(k5_relat_1(sK3,sK89),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK89,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_367])])).

fof(f14201,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK89,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f3925])).

fof(f28251,plain,
    ( spl206_324
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14209,f8752,f28030])).

fof(f28030,plain,
    ( spl206_324
  <=> k5_relat_1(k5_relat_1(sK3,sK89),sK3) = k5_relat_1(sK3,k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_324])])).

fof(f14209,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),sK3) = k5_relat_1(sK3,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f3925])).

fof(f28250,plain,
    ( spl206_366
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14216,f8752,f28247])).

fof(f28247,plain,
    ( spl206_366
  <=> k5_relat_1(k5_relat_1(sK3,sK89),sK89) = k5_relat_1(sK3,k5_relat_1(sK89,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_366])])).

fof(f14216,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),sK89) = k5_relat_1(sK3,k5_relat_1(sK89,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f3925])).

fof(f28245,plain,
    ( spl206_365
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14217,f8752,f28242])).

fof(f28242,plain,
    ( spl206_365
  <=> k5_relat_1(k5_relat_1(sK3,sK89),sK128) = k5_relat_1(sK3,k5_relat_1(sK89,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_365])])).

fof(f14217,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),sK128) = k5_relat_1(sK3,k5_relat_1(sK89,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f3925])).

fof(f28240,plain,
    ( spl206_364
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14218,f8752,f28237])).

fof(f28237,plain,
    ( spl206_364
  <=> k5_relat_1(k5_relat_1(sK3,sK89),sK162) = k5_relat_1(sK3,k5_relat_1(sK89,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_364])])).

fof(f14218,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),sK162) = k5_relat_1(sK3,k5_relat_1(sK89,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f3925])).

fof(f28235,plain,
    ( spl206_363
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14223,f8752,f28232])).

fof(f28232,plain,
    ( spl206_363
  <=> k5_relat_1(k5_relat_1(sK3,sK128),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK128,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_363])])).

fof(f14223,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK128,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f3925])).

fof(f28230,plain,
    ( spl206_319
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14231,f8752,f28005])).

fof(f28005,plain,
    ( spl206_319
  <=> k5_relat_1(k5_relat_1(sK3,sK128),sK3) = k5_relat_1(sK3,k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_319])])).

fof(f14231,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),sK3) = k5_relat_1(sK3,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f3925])).

fof(f28229,plain,
    ( spl206_362
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14238,f8752,f28226])).

fof(f28226,plain,
    ( spl206_362
  <=> k5_relat_1(k5_relat_1(sK3,sK128),sK89) = k5_relat_1(sK3,k5_relat_1(sK128,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_362])])).

fof(f14238,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),sK89) = k5_relat_1(sK3,k5_relat_1(sK128,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f3925])).

fof(f28224,plain,
    ( spl206_361
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14239,f8752,f28221])).

fof(f28221,plain,
    ( spl206_361
  <=> k5_relat_1(k5_relat_1(sK3,sK128),sK128) = k5_relat_1(sK3,k5_relat_1(sK128,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_361])])).

fof(f14239,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),sK128) = k5_relat_1(sK3,k5_relat_1(sK128,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f3925])).

fof(f28219,plain,
    ( spl206_360
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14240,f8752,f28216])).

fof(f28216,plain,
    ( spl206_360
  <=> k5_relat_1(k5_relat_1(sK3,sK128),sK162) = k5_relat_1(sK3,k5_relat_1(sK128,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_360])])).

fof(f14240,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),sK162) = k5_relat_1(sK3,k5_relat_1(sK128,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f3925])).

fof(f28214,plain,
    ( spl206_359
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14245,f8752,f28211])).

fof(f28211,plain,
    ( spl206_359
  <=> k5_relat_1(k5_relat_1(sK3,sK162),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK162,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_359])])).

fof(f14245,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK162,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f3925])).

fof(f28209,plain,
    ( spl206_314
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14253,f8752,f27980])).

fof(f27980,plain,
    ( spl206_314
  <=> k5_relat_1(k5_relat_1(sK3,sK162),sK3) = k5_relat_1(sK3,k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_314])])).

fof(f14253,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),sK3) = k5_relat_1(sK3,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f3925])).

fof(f28208,plain,
    ( spl206_358
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14260,f8752,f28205])).

fof(f28205,plain,
    ( spl206_358
  <=> k5_relat_1(k5_relat_1(sK3,sK162),sK89) = k5_relat_1(sK3,k5_relat_1(sK162,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_358])])).

fof(f14260,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),sK89) = k5_relat_1(sK3,k5_relat_1(sK162,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f3925])).

fof(f28203,plain,
    ( spl206_357
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14261,f8752,f28200])).

fof(f28200,plain,
    ( spl206_357
  <=> k5_relat_1(k5_relat_1(sK3,sK162),sK128) = k5_relat_1(sK3,k5_relat_1(sK162,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_357])])).

fof(f14261,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),sK128) = k5_relat_1(sK3,k5_relat_1(sK162,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f3925])).

fof(f28198,plain,
    ( spl206_356
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14262,f8752,f28195])).

fof(f28195,plain,
    ( spl206_356
  <=> k5_relat_1(k5_relat_1(sK3,sK162),sK162) = k5_relat_1(sK3,k5_relat_1(sK162,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_356])])).

fof(f14262,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),sK162) = k5_relat_1(sK3,k5_relat_1(sK162,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f3925])).

fof(f28193,plain,
    ( spl206_355
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14355,f8752,f28190])).

fof(f28190,plain,
    ( spl206_355
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK3),k1_xboole_0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_355])])).

fof(f14355,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),k1_xboole_0) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f3925])).

fof(f28188,plain,
    ( spl206_354
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14363,f8752,f28185])).

fof(f14363,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),k1_xboole_0) = k5_relat_1(sK3,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f3925])).

fof(f28183,plain,
    ( spl206_353
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14370,f8752,f28180])).

fof(f28180,plain,
    ( spl206_353
  <=> k5_relat_1(k5_relat_1(sK89,sK3),k1_xboole_0) = k5_relat_1(sK89,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_353])])).

fof(f14370,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),k1_xboole_0) = k5_relat_1(sK89,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f3925])).

fof(f28178,plain,
    ( spl206_352
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14371,f8752,f28175])).

fof(f28175,plain,
    ( spl206_352
  <=> k5_relat_1(k5_relat_1(sK128,sK3),k1_xboole_0) = k5_relat_1(sK128,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_352])])).

fof(f14371,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),k1_xboole_0) = k5_relat_1(sK128,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f3925])).

fof(f28173,plain,
    ( spl206_351
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14372,f8752,f28170])).

fof(f28170,plain,
    ( spl206_351
  <=> k5_relat_1(k5_relat_1(sK162,sK3),k1_xboole_0) = k5_relat_1(sK162,k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_351])])).

fof(f14372,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),k1_xboole_0) = k5_relat_1(sK162,k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f3925])).

fof(f28168,plain,
    ( spl206_330
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14531,f8752,f28060])).

fof(f28060,plain,
    ( spl206_330
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_330])])).

fof(f14531,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f3925])).

fof(f28167,plain,
    ( spl206_329
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14539,f8752,f28055])).

fof(f14539,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK3) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f3925])).

fof(f28166,plain,
    ( spl206_328
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14546,f8752,f28050])).

fof(f28050,plain,
    ( spl206_328
  <=> k5_relat_1(k5_relat_1(sK89,sK3),sK3) = k5_relat_1(sK89,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_328])])).

fof(f14546,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),sK3) = k5_relat_1(sK89,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f3925])).

fof(f28165,plain,
    ( spl206_327
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14547,f8752,f28045])).

fof(f28045,plain,
    ( spl206_327
  <=> k5_relat_1(k5_relat_1(sK128,sK3),sK3) = k5_relat_1(sK128,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_327])])).

fof(f14547,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),sK3) = k5_relat_1(sK128,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f3925])).

fof(f28164,plain,
    ( spl206_326
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14548,f8752,f28040])).

fof(f28040,plain,
    ( spl206_326
  <=> k5_relat_1(k5_relat_1(sK162,sK3),sK3) = k5_relat_1(sK162,k5_relat_1(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_326])])).

fof(f14548,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),sK3) = k5_relat_1(sK162,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f3925])).

fof(f28163,plain,
    ( spl206_350
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14685,f8752,f28160])).

fof(f28160,plain,
    ( spl206_350
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK89) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_350])])).

fof(f14685,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK89) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f3925])).

fof(f28158,plain,
    ( spl206_349
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14693,f8752,f28155])).

fof(f14693,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK89) = k5_relat_1(sK3,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f3925])).

fof(f28153,plain,
    ( spl206_348
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14700,f8752,f28150])).

fof(f28150,plain,
    ( spl206_348
  <=> k5_relat_1(k5_relat_1(sK89,sK3),sK89) = k5_relat_1(sK89,k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_348])])).

fof(f14700,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),sK89) = k5_relat_1(sK89,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f3925])).

fof(f28148,plain,
    ( spl206_347
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14701,f8752,f28145])).

fof(f28145,plain,
    ( spl206_347
  <=> k5_relat_1(k5_relat_1(sK128,sK3),sK89) = k5_relat_1(sK128,k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_347])])).

fof(f14701,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),sK89) = k5_relat_1(sK128,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f3925])).

fof(f28143,plain,
    ( spl206_346
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14702,f8752,f28140])).

fof(f28140,plain,
    ( spl206_346
  <=> k5_relat_1(k5_relat_1(sK162,sK3),sK89) = k5_relat_1(sK162,k5_relat_1(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_346])])).

fof(f14702,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),sK89) = k5_relat_1(sK162,k5_relat_1(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f3925])).

fof(f28138,plain,
    ( spl206_345
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14707,f8752,f28135])).

fof(f28135,plain,
    ( spl206_345
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK128) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_345])])).

fof(f14707,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK128) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f3925])).

fof(f28133,plain,
    ( spl206_344
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14715,f8752,f28130])).

fof(f14715,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK128) = k5_relat_1(sK3,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f3925])).

fof(f28128,plain,
    ( spl206_343
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14722,f8752,f28125])).

fof(f28125,plain,
    ( spl206_343
  <=> k5_relat_1(k5_relat_1(sK89,sK3),sK128) = k5_relat_1(sK89,k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_343])])).

fof(f14722,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),sK128) = k5_relat_1(sK89,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f3925])).

fof(f28123,plain,
    ( spl206_342
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14723,f8752,f28120])).

fof(f28120,plain,
    ( spl206_342
  <=> k5_relat_1(k5_relat_1(sK128,sK3),sK128) = k5_relat_1(sK128,k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_342])])).

fof(f14723,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),sK128) = k5_relat_1(sK128,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f3925])).

fof(f28118,plain,
    ( spl206_341
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14724,f8752,f28115])).

fof(f28115,plain,
    ( spl206_341
  <=> k5_relat_1(k5_relat_1(sK162,sK3),sK128) = k5_relat_1(sK162,k5_relat_1(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_341])])).

fof(f14724,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),sK128) = k5_relat_1(sK162,k5_relat_1(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f3925])).

fof(f28113,plain,
    ( spl206_340
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14729,f8752,f28110])).

fof(f28110,plain,
    ( spl206_340
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK162) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_340])])).

fof(f14729,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK162) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f3925])).

fof(f28108,plain,
    ( spl206_339
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14737,f8752,f28105])).

fof(f14737,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK162) = k5_relat_1(sK3,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f3925])).

fof(f28103,plain,
    ( spl206_338
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14744,f8752,f28100])).

fof(f28100,plain,
    ( spl206_338
  <=> k5_relat_1(k5_relat_1(sK89,sK3),sK162) = k5_relat_1(sK89,k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_338])])).

fof(f14744,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),sK162) = k5_relat_1(sK89,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f3925])).

fof(f28098,plain,
    ( spl206_337
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14745,f8752,f28095])).

fof(f28095,plain,
    ( spl206_337
  <=> k5_relat_1(k5_relat_1(sK128,sK3),sK162) = k5_relat_1(sK128,k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_337])])).

fof(f14745,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),sK162) = k5_relat_1(sK128,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f3925])).

fof(f28093,plain,
    ( spl206_336
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14746,f8752,f28090])).

fof(f28090,plain,
    ( spl206_336
  <=> k5_relat_1(k5_relat_1(sK162,sK3),sK162) = k5_relat_1(sK162,k5_relat_1(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_336])])).

fof(f14746,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),sK162) = k5_relat_1(sK162,k5_relat_1(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f3925])).

fof(f28088,plain,
    ( spl206_335
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14839,f8752,f28085])).

fof(f28085,plain,
    ( spl206_335
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_335])])).

fof(f14839,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,k1_xboole_0),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f3925])).

fof(f28083,plain,
    ( spl206_334
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14847,f8752,f28080])).

fof(f14847,plain,
    ( k5_relat_1(k5_relat_1(sK3,k1_xboole_0),sK3) = k5_relat_1(sK3,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f3925])).

fof(f28078,plain,
    ( spl206_333
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14854,f8752,f28075])).

fof(f28075,plain,
    ( spl206_333
  <=> k5_relat_1(k5_relat_1(sK89,k1_xboole_0),sK3) = k5_relat_1(sK89,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_333])])).

fof(f14854,plain,
    ( k5_relat_1(k5_relat_1(sK89,k1_xboole_0),sK3) = k5_relat_1(sK89,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f3925])).

fof(f28073,plain,
    ( spl206_332
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14855,f8752,f28070])).

fof(f28070,plain,
    ( spl206_332
  <=> k5_relat_1(k5_relat_1(sK128,k1_xboole_0),sK3) = k5_relat_1(sK128,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_332])])).

fof(f14855,plain,
    ( k5_relat_1(k5_relat_1(sK128,k1_xboole_0),sK3) = k5_relat_1(sK128,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f3925])).

fof(f28068,plain,
    ( spl206_331
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f14856,f8752,f28065])).

fof(f28065,plain,
    ( spl206_331
  <=> k5_relat_1(k5_relat_1(sK162,k1_xboole_0),sK3) = k5_relat_1(sK162,k5_relat_1(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_331])])).

fof(f14856,plain,
    ( k5_relat_1(k5_relat_1(sK162,k1_xboole_0),sK3) = k5_relat_1(sK162,k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f3925])).

fof(f28063,plain,
    ( spl206_330
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15015,f8752,f28060])).

fof(f15015,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK3),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f3925])).

fof(f28058,plain,
    ( spl206_329
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15023,f8752,f28055])).

fof(f15023,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK3),sK3) = k5_relat_1(sK3,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f3925])).

fof(f28053,plain,
    ( spl206_328
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15030,f8752,f28050])).

fof(f15030,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK3),sK3) = k5_relat_1(sK89,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f3925])).

fof(f28048,plain,
    ( spl206_327
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15031,f8752,f28045])).

fof(f15031,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK3),sK3) = k5_relat_1(sK128,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f3925])).

fof(f28043,plain,
    ( spl206_326
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15032,f8752,f28040])).

fof(f15032,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK3),sK3) = k5_relat_1(sK162,k5_relat_1(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f3925])).

fof(f28038,plain,
    ( spl206_325
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15169,f8752,f28035])).

fof(f28035,plain,
    ( spl206_325
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK89),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_325])])).

fof(f15169,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK89),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f3925])).

fof(f28033,plain,
    ( spl206_324
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15177,f8752,f28030])).

fof(f15177,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK89),sK3) = k5_relat_1(sK3,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f3925])).

fof(f28028,plain,
    ( spl206_323
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15184,f8752,f28025])).

fof(f28025,plain,
    ( spl206_323
  <=> k5_relat_1(k5_relat_1(sK89,sK89),sK3) = k5_relat_1(sK89,k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_323])])).

fof(f15184,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK89),sK3) = k5_relat_1(sK89,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f3925])).

fof(f28023,plain,
    ( spl206_322
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15185,f8752,f28020])).

fof(f28020,plain,
    ( spl206_322
  <=> k5_relat_1(k5_relat_1(sK128,sK89),sK3) = k5_relat_1(sK128,k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_322])])).

fof(f15185,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK89),sK3) = k5_relat_1(sK128,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f3925])).

fof(f28018,plain,
    ( spl206_321
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15186,f8752,f28015])).

fof(f28015,plain,
    ( spl206_321
  <=> k5_relat_1(k5_relat_1(sK162,sK89),sK3) = k5_relat_1(sK162,k5_relat_1(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_321])])).

fof(f15186,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK89),sK3) = k5_relat_1(sK162,k5_relat_1(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f3925])).

fof(f28013,plain,
    ( spl206_320
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15191,f8752,f28010])).

fof(f28010,plain,
    ( spl206_320
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK128),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_320])])).

fof(f15191,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK128),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f3925])).

fof(f28008,plain,
    ( spl206_319
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15199,f8752,f28005])).

fof(f15199,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK128),sK3) = k5_relat_1(sK3,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f3925])).

fof(f28003,plain,
    ( spl206_318
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15206,f8752,f28000])).

fof(f28000,plain,
    ( spl206_318
  <=> k5_relat_1(k5_relat_1(sK89,sK128),sK3) = k5_relat_1(sK89,k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_318])])).

fof(f15206,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK128),sK3) = k5_relat_1(sK89,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f3925])).

fof(f27998,plain,
    ( spl206_317
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15207,f8752,f27995])).

fof(f27995,plain,
    ( spl206_317
  <=> k5_relat_1(k5_relat_1(sK128,sK128),sK3) = k5_relat_1(sK128,k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_317])])).

fof(f15207,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK128),sK3) = k5_relat_1(sK128,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f3925])).

fof(f27993,plain,
    ( spl206_316
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15208,f8752,f27990])).

fof(f27990,plain,
    ( spl206_316
  <=> k5_relat_1(k5_relat_1(sK162,sK128),sK3) = k5_relat_1(sK162,k5_relat_1(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_316])])).

fof(f15208,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK128),sK3) = k5_relat_1(sK162,k5_relat_1(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f3925])).

fof(f27988,plain,
    ( spl206_315
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15213,f8752,f27985])).

fof(f27985,plain,
    ( spl206_315
  <=> k5_relat_1(k5_relat_1(k1_xboole_0,sK162),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_315])])).

fof(f15213,plain,
    ( k5_relat_1(k5_relat_1(k1_xboole_0,sK162),sK3) = k5_relat_1(k1_xboole_0,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f3925])).

fof(f27983,plain,
    ( spl206_314
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15221,f8752,f27980])).

fof(f15221,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK162),sK3) = k5_relat_1(sK3,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f3925])).

fof(f27978,plain,
    ( spl206_313
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15228,f8752,f27975])).

fof(f27975,plain,
    ( spl206_313
  <=> k5_relat_1(k5_relat_1(sK89,sK162),sK3) = k5_relat_1(sK89,k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_313])])).

fof(f15228,plain,
    ( k5_relat_1(k5_relat_1(sK89,sK162),sK3) = k5_relat_1(sK89,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f3925])).

fof(f27973,plain,
    ( spl206_312
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15229,f8752,f27970])).

fof(f27970,plain,
    ( spl206_312
  <=> k5_relat_1(k5_relat_1(sK128,sK162),sK3) = k5_relat_1(sK128,k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_312])])).

fof(f15229,plain,
    ( k5_relat_1(k5_relat_1(sK128,sK162),sK3) = k5_relat_1(sK128,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f3925])).

fof(f27968,plain,
    ( spl206_311
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15230,f8752,f27965])).

fof(f27965,plain,
    ( spl206_311
  <=> k5_relat_1(k5_relat_1(sK162,sK162),sK3) = k5_relat_1(sK162,k5_relat_1(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_311])])).

fof(f15230,plain,
    ( k5_relat_1(k5_relat_1(sK162,sK162),sK3) = k5_relat_1(sK162,k5_relat_1(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f3925])).

fof(f27961,plain,
    ( spl206_310
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15365,f8752,f5107,f27958])).

fof(f27958,plain,
    ( spl206_310
  <=> k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_310])])).

fof(f15365,plain,
    ( k2_wellord1(sK3,sK1) = k2_wellord1(k2_wellord1(sK3,sK2),sK1)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f3930])).

fof(f3930,plain,(
    ! [X2,X0,X1] :
      ( k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2038])).

fof(f2038,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2037])).

fof(f2037,plain,(
    ! [X0,X1,X2] :
      ( k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1173])).

fof(f1173,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k2_wellord1(X2,X0) = k2_wellord1(k2_wellord1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

fof(f27956,plain,
    ( ~ spl206_309
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15368,f8752,f27953])).

fof(f27953,plain,
    ( spl206_309
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_309])])).

fof(f15368,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4021,f8754,f3934])).

fof(f3934,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_relat_1(X0))
      | ~ r2_hidden(X3,sK163(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2630])).

fof(f2630,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( ( r2_hidden(X3,sK163(X0,X1))
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,sK164(X0,X1,X3))))
              & r2_hidden(sK164(X0,X1,X3),k3_relat_1(X1))
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK163(X0,X1)) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK163,sK164])],[f2627,f2629,f2628])).

fof(f2628,plain,(
    ! [X1,X0] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ? [X5] :
                  ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X5)))
                  & r2_hidden(X5,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
     => ! [X3] :
          ( ( r2_hidden(X3,sK163(X0,X1))
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ? [X5] :
                  ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X5)))
                  & r2_hidden(X5,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,sK163(X0,X1)) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2629,plain,(
    ! [X3,X1,X0] :
      ( ? [X5] :
          ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X5)))
          & r2_hidden(X5,k3_relat_1(X1)) )
     => ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,sK164(X0,X1,X3))))
        & r2_hidden(sK164(X0,X1,X3),k3_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2627,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ? [X5] :
                  ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X5)))
                  & r2_hidden(X5,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f2626])).

fof(f2626,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ? [X4] :
                  ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                  & r2_hidden(X4,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2625])).

fof(f2625,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( ( r2_hidden(X3,X2)
            | ! [X4] :
                ( ~ r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                | ~ r2_hidden(X4,k3_relat_1(X1)) )
            | ~ r2_hidden(X3,k3_relat_1(X0)) )
          & ( ( ? [X4] :
                  ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                  & r2_hidden(X4,k3_relat_1(X1)) )
              & r2_hidden(X3,k3_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f2043])).

fof(f2043,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ? [X4] :
                ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                & r2_hidden(X4,k3_relat_1(X1)) )
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f2042])).

fof(f2042,plain,(
    ! [X0,X1] :
      ( ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ? [X4] :
                ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                & r2_hidden(X4,k3_relat_1(X1)) )
            & r2_hidden(X3,k3_relat_1(X0)) ) )
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1155])).

fof(f1155,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => ? [X2] :
        ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ? [X4] :
                ( r4_wellord1(k2_wellord1(X0,k1_wellord1(X0,X3)),k2_wellord1(X1,k1_wellord1(X1,X4)))
                & r2_hidden(X4,k3_relat_1(X1)) )
            & r2_hidden(X3,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',s1_xboole_0__e6_74__wellord1)).

fof(f27951,plain,
    ( ~ spl206_304
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15376,f8752,f27925])).

fof(f27925,plain,
    ( spl206_304
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_304])])).

fof(f15376,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4021,f8754,f3934])).

fof(f27950,plain,
    ( ~ spl206_308
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15383,f8752,f27947])).

fof(f27947,plain,
    ( spl206_308
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_308])])).

fof(f15383,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4021,f8754,f3934])).

fof(f27945,plain,
    ( ~ spl206_307
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15384,f8752,f27942])).

fof(f27942,plain,
    ( spl206_307
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_307])])).

fof(f15384,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4021,f8754,f3934])).

fof(f27940,plain,
    ( ~ spl206_306
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15385,f8752,f27937])).

fof(f27937,plain,
    ( spl206_306
  <=> r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_306])])).

fof(f15385,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4021,f8754,f3934])).

fof(f27935,plain,
    ( ~ spl206_305
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27930,f8752,f27932])).

fof(f27932,plain,
    ( spl206_305
  <=> r2_hidden(sK177(k1_xboole_0),sK163(k1_xboole_0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_305])])).

fof(f27930,plain,
    ( ~ r2_hidden(sK177(k1_xboole_0),sK163(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15390,f3765])).

fof(f3765,plain,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f858])).

fof(f858,axiom,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f15390,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(k1_xboole_0)),sK163(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4021,f8754,f3934])).

fof(f27928,plain,
    ( ~ spl206_304
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15398,f8752,f27925])).

fof(f15398,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK3)),sK163(sK3,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4021,f8754,f3934])).

fof(f27923,plain,
    ( ~ spl206_303
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15405,f8752,f27920])).

fof(f27920,plain,
    ( spl206_303
  <=> r2_hidden(sK177(k3_relat_1(sK89)),sK163(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_303])])).

fof(f15405,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK89)),sK163(sK89,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4021,f8754,f3934])).

fof(f27918,plain,
    ( ~ spl206_302
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15406,f8752,f27915])).

fof(f27915,plain,
    ( spl206_302
  <=> r2_hidden(sK177(k3_relat_1(sK128)),sK163(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_302])])).

fof(f15406,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK128)),sK163(sK128,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4021,f8754,f3934])).

fof(f27913,plain,
    ( ~ spl206_301
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15407,f8752,f27910])).

fof(f27910,plain,
    ( spl206_301
  <=> r2_hidden(sK177(k3_relat_1(sK162)),sK163(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_301])])).

fof(f15407,plain,
    ( ~ r2_hidden(sK177(k3_relat_1(sK162)),sK163(sK162,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4021,f8754,f3934])).

fof(f27908,plain,
    ( spl206_300
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27903,f8752,f27905])).

fof(f27905,plain,
    ( spl206_300
  <=> k4_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_300])])).

fof(f27903,plain,
    ( k4_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k5_relat_1(k1_xboole_0,k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15414,f4240])).

fof(f4240,plain,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f861])).

fof(f861,axiom,(
    k1_xboole_0 = k4_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_relat_1)).

fof(f15414,plain,
    ( k4_relat_1(k5_relat_1(sK3,k1_xboole_0)) = k5_relat_1(k4_relat_1(k1_xboole_0),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4232])).

fof(f4232,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2143])).

fof(f2143,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f853])).

fof(f853,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f27898,plain,
    ( spl206_295
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15422,f8752,f27869])).

fof(f27869,plain,
    ( spl206_295
  <=> k4_relat_1(k5_relat_1(sK3,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_295])])).

fof(f15422,plain,
    ( k4_relat_1(k5_relat_1(sK3,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4232])).

fof(f27897,plain,
    ( spl206_299
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15429,f8752,f27894])).

fof(f27894,plain,
    ( spl206_299
  <=> k4_relat_1(k5_relat_1(sK3,sK89)) = k5_relat_1(k4_relat_1(sK89),k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_299])])).

fof(f15429,plain,
    ( k4_relat_1(k5_relat_1(sK3,sK89)) = k5_relat_1(k4_relat_1(sK89),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4232])).

fof(f27892,plain,
    ( spl206_298
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15430,f8752,f27889])).

fof(f27889,plain,
    ( spl206_298
  <=> k4_relat_1(k5_relat_1(sK3,sK128)) = k5_relat_1(k4_relat_1(sK128),k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_298])])).

fof(f15430,plain,
    ( k4_relat_1(k5_relat_1(sK3,sK128)) = k5_relat_1(k4_relat_1(sK128),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4232])).

fof(f27887,plain,
    ( spl206_297
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15431,f8752,f27884])).

fof(f27884,plain,
    ( spl206_297
  <=> k4_relat_1(k5_relat_1(sK3,sK162)) = k5_relat_1(k4_relat_1(sK162),k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_297])])).

fof(f15431,plain,
    ( k4_relat_1(k5_relat_1(sK3,sK162)) = k5_relat_1(k4_relat_1(sK162),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4232])).

fof(f27882,plain,
    ( spl206_296
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27877,f8752,f27879])).

fof(f27879,plain,
    ( spl206_296
  <=> k4_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k5_relat_1(k4_relat_1(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_296])])).

fof(f27877,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k5_relat_1(k4_relat_1(sK3),k1_xboole_0)
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15436,f4240])).

fof(f15436,plain,
    ( k4_relat_1(k5_relat_1(k1_xboole_0,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4232])).

fof(f27872,plain,
    ( spl206_295
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15444,f8752,f27869])).

fof(f15444,plain,
    ( k4_relat_1(k5_relat_1(sK3,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4232])).

fof(f27867,plain,
    ( spl206_294
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15451,f8752,f27864])).

fof(f27864,plain,
    ( spl206_294
  <=> k4_relat_1(k5_relat_1(sK89,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_294])])).

fof(f15451,plain,
    ( k4_relat_1(k5_relat_1(sK89,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4232])).

fof(f27862,plain,
    ( spl206_293
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15452,f8752,f27859])).

fof(f27859,plain,
    ( spl206_293
  <=> k4_relat_1(k5_relat_1(sK128,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_293])])).

fof(f15452,plain,
    ( k4_relat_1(k5_relat_1(sK128,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4232])).

fof(f27857,plain,
    ( spl206_292
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15453,f8752,f27854])).

fof(f27854,plain,
    ( spl206_292
  <=> k4_relat_1(k5_relat_1(sK162,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_292])])).

fof(f15453,plain,
    ( k4_relat_1(k5_relat_1(sK162,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4232])).

fof(f27833,plain,
    ( spl206_288
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27832,f8752,f27780])).

fof(f27780,plain,
    ( spl206_288
  <=> k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK3,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_288])])).

fof(f27832,plain,
    ( k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK3,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15466,f4247])).

fof(f4247,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f493])).

fof(f493,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f15466,plain,
    ( k4_relat_1(k6_subset_1(sK3,sK3)) = k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4233])).

fof(f4233,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2144])).

fof(f2144,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f842])).

fof(f842,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k6_subset_1(X0,X1)) = k6_subset_1(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_relat_1)).

fof(f27825,plain,
    ( spl206_291
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27820,f8752,f27822])).

fof(f27822,plain,
    ( spl206_291
  <=> k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK89)) = k4_relat_1(k4_xboole_0(sK3,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_291])])).

fof(f27820,plain,
    ( k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK89)) = k4_relat_1(k4_xboole_0(sK3,sK89))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15473,f4247])).

fof(f15473,plain,
    ( k4_relat_1(k6_subset_1(sK3,sK89)) = k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK89))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4233])).

fof(f27819,plain,
    ( spl206_290
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27814,f8752,f27816])).

fof(f27816,plain,
    ( spl206_290
  <=> k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK128)) = k4_relat_1(k4_xboole_0(sK3,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_290])])).

fof(f27814,plain,
    ( k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK128)) = k4_relat_1(k4_xboole_0(sK3,sK128))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15474,f4247])).

fof(f15474,plain,
    ( k4_relat_1(k6_subset_1(sK3,sK128)) = k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK128))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4233])).

fof(f27813,plain,
    ( spl206_289
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27808,f8752,f27810])).

fof(f27810,plain,
    ( spl206_289
  <=> k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK162)) = k4_relat_1(k4_xboole_0(sK3,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_289])])).

fof(f27808,plain,
    ( k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK162)) = k4_relat_1(k4_xboole_0(sK3,sK162))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15475,f4247])).

fof(f15475,plain,
    ( k4_relat_1(k6_subset_1(sK3,sK162)) = k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK162))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4233])).

fof(f27783,plain,
    ( spl206_288
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27778,f8752,f27780])).

fof(f27778,plain,
    ( k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK3,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15488,f4247])).

fof(f15488,plain,
    ( k4_relat_1(k6_subset_1(sK3,sK3)) = k6_subset_1(k4_relat_1(sK3),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4233])).

fof(f27771,plain,
    ( spl206_287
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27766,f8752,f27768])).

fof(f27768,plain,
    ( spl206_287
  <=> k6_subset_1(k4_relat_1(sK89),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK89,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_287])])).

fof(f27766,plain,
    ( k6_subset_1(k4_relat_1(sK89),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK89,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15495,f4247])).

fof(f15495,plain,
    ( k4_relat_1(k6_subset_1(sK89,sK3)) = k6_subset_1(k4_relat_1(sK89),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4233])).

fof(f27765,plain,
    ( spl206_286
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27760,f8752,f27762])).

fof(f27762,plain,
    ( spl206_286
  <=> k6_subset_1(k4_relat_1(sK128),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK128,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_286])])).

fof(f27760,plain,
    ( k6_subset_1(k4_relat_1(sK128),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK128,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15496,f4247])).

fof(f15496,plain,
    ( k4_relat_1(k6_subset_1(sK128,sK3)) = k6_subset_1(k4_relat_1(sK128),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4233])).

fof(f27759,plain,
    ( spl206_285
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27754,f8752,f27756])).

fof(f27756,plain,
    ( spl206_285
  <=> k6_subset_1(k4_relat_1(sK162),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK162,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_285])])).

fof(f27754,plain,
    ( k6_subset_1(k4_relat_1(sK162),k4_relat_1(sK3)) = k4_relat_1(k4_xboole_0(sK162,sK3))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15497,f4247])).

fof(f15497,plain,
    ( k4_relat_1(k6_subset_1(sK162,sK3)) = k6_subset_1(k4_relat_1(sK162),k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4233])).

fof(f27749,plain,
    ( spl206_284
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15502,f8752,f27746])).

fof(f27746,plain,
    ( spl206_284
  <=> k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_284])])).

fof(f15502,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4234])).

fof(f4234,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2145])).

fof(f2145,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f838])).

fof(f838,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f27744,plain,
    ( spl206_283
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15503,f8752,f27741])).

fof(f27741,plain,
    ( spl206_283
  <=> k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_283])])).

fof(f15503,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4235])).

fof(f4235,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2145])).

fof(f27739,plain,
    ( spl206_282
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15504,f8752,f27736])).

fof(f27736,plain,
    ( spl206_282
  <=> sK3 = k4_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_282])])).

fof(f15504,plain,
    ( sK3 = k4_relat_1(k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4236])).

fof(f4236,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2146])).

fof(f2146,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f700])).

fof(f700,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

fof(f27734,plain,
    ( spl206_281
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f15505,f8752,f27731])).

fof(f27731,plain,
    ( spl206_281
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_281])])).

fof(f15505,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4237])).

fof(f4237,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2147])).

fof(f2147,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f666])).

fof(f666,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f27677,plain,
    ( spl206_280
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27672,f8752,f5107,f27674])).

fof(f27674,plain,
    ( spl206_280
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK3,k7_relat_1(sK3,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_280])])).

fof(f27672,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK3,k7_relat_1(sK3,sK2)),sK1)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15552,f4247])).

fof(f15552,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK3,k7_relat_1(sK3,sK2)),sK1)
    | ~ spl206_2
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f5109,f8754,f4242])).

fof(f4242,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2152])).

fof(f2152,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2151])).

fof(f2151,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f821])).

fof(f821,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k1_xboole_0 = k7_relat_1(k6_subset_1(X2,k7_relat_1(X2,X1)),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t216_relat_1)).

fof(f27268,plain,
    ( spl206_254
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27267,f8752,f25135])).

fof(f25135,plain,
    ( spl206_254
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_254])])).

fof(f27267,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f27266,f4247])).

fof(f27266,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15741,f4247])).

fof(f15741,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f4249])).

fof(f4249,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2157])).

fof(f2157,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2)))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f852])).

fof(f852,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k6_subset_1(k5_relat_1(X0,X1),k5_relat_1(X0,X2)),k5_relat_1(X0,k6_subset_1(X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_relat_1)).

fof(f27253,plain,
    ( spl206_269
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27252,f8752,f25892])).

fof(f25892,plain,
    ( spl206_269
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_269])])).

fof(f27252,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f27251,f4247])).

fof(f27251,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15748,f4247])).

fof(f15748,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f4249])).

fof(f27250,plain,
    ( spl206_264
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27249,f8752,f25823])).

fof(f25823,plain,
    ( spl206_264
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_264])])).

fof(f27249,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f27248,f4247])).

fof(f27248,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15749,f4247])).

fof(f15749,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f4249])).

fof(f27247,plain,
    ( spl206_259
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f27246,f8752,f25754])).

fof(f25754,plain,
    ( spl206_259
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_259])])).

fof(f27246,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f27245,f4247])).

fof(f27245,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15750,f4247])).

fof(f15750,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f4249])).

fof(f26949,plain,
    ( spl206_249
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26948,f8752,f24802])).

fof(f24802,plain,
    ( spl206_249
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_249])])).

fof(f26948,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26947,f4247])).

fof(f26947,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15895,f4247])).

fof(f15895,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4249])).

fof(f26934,plain,
    ( spl206_279
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26929,f8752,f26931])).

fof(f26931,plain,
    ( spl206_279
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK89,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_279])])).

fof(f26929,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK89,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26928,f4247])).

fof(f26928,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK89,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15902,f4247])).

fof(f15902,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k6_subset_1(sK89,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4249])).

fof(f26927,plain,
    ( spl206_278
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26922,f8752,f26924])).

% (25623)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_138 on theBenchmark
fof(f26924,plain,
    ( spl206_278
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK89,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_278])])).

fof(f26922,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK89,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26921,f4247])).

fof(f26921,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK89,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15903,f4247])).

fof(f15903,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k6_subset_1(sK89,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4249])).

fof(f26920,plain,
    ( spl206_277
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26915,f8752,f26917])).

fof(f26917,plain,
    ( spl206_277
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK89,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_277])])).

fof(f26915,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK89,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26914,f4247])).

fof(f26914,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK89,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15904,f4247])).

fof(f15904,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k6_subset_1(sK89,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4249])).

fof(f26888,plain,
    ( spl206_244
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26887,f8752,f24733])).

fof(f24733,plain,
    ( spl206_244
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_244])])).

fof(f26887,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26886,f4247])).

fof(f26886,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15917,f4247])).

fof(f15917,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4249])).

fof(f26873,plain,
    ( spl206_276
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26868,f8752,f26870])).

fof(f26870,plain,
    ( spl206_276
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK128,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_276])])).

fof(f26868,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK128,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26867,f4247])).

fof(f26867,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK128,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15924,f4247])).

fof(f15924,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k6_subset_1(sK128,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4249])).

fof(f26866,plain,
    ( spl206_275
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26861,f8752,f26863])).

fof(f26863,plain,
    ( spl206_275
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK128,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_275])])).

fof(f26861,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK128,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26860,f4247])).

fof(f26860,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK128,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15925,f4247])).

fof(f15925,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k6_subset_1(sK128,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4249])).

fof(f26859,plain,
    ( spl206_274
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26854,f8752,f26856])).

fof(f26856,plain,
    ( spl206_274
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK128,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_274])])).

fof(f26854,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK128,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26853,f4247])).

fof(f26853,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK128,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15926,f4247])).

fof(f15926,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k6_subset_1(sK128,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4249])).

fof(f26827,plain,
    ( spl206_239
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26826,f8752,f24664])).

fof(f24664,plain,
    ( spl206_239
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_239])])).

fof(f26826,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26825,f4247])).

fof(f26825,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15939,f4247])).

fof(f15939,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4249])).

fof(f26812,plain,
    ( spl206_273
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26807,f8752,f26809])).

fof(f26809,plain,
    ( spl206_273
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK162,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_273])])).

fof(f26807,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK162,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26806,f4247])).

fof(f26806,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK162,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15946,f4247])).

fof(f15946,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k6_subset_1(sK162,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4249])).

fof(f26805,plain,
    ( spl206_272
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26800,f8752,f26802])).

fof(f26802,plain,
    ( spl206_272
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK162,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_272])])).

fof(f26800,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK162,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26799,f4247])).

fof(f26799,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK162,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15947,f4247])).

fof(f15947,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k6_subset_1(sK162,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4249])).

fof(f26798,plain,
    ( spl206_271
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26793,f8752,f26795])).

fof(f26795,plain,
    ( spl206_271
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK162,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_271])])).

fof(f26793,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK162,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26792,f4247])).

fof(f26792,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK162,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f15948,f4247])).

fof(f15948,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k6_subset_1(sK162,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4249])).

fof(f26229,plain,
    ( spl206_255
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26228,f8752,f25156])).

fof(f25156,plain,
    ( spl206_255
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_255])])).

fof(f26228,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26227,f4247])).

fof(f26227,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16217,f4247])).

fof(f16217,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f4249])).

fof(f26212,plain,
    ( spl206_254
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26211,f8752,f25135])).

fof(f26211,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26210,f4247])).

fof(f26210,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16225,f4247])).

fof(f16225,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f4249])).

fof(f26197,plain,
    ( spl206_253
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26196,f8752,f25116])).

fof(f25116,plain,
    ( spl206_253
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_253])])).

fof(f26196,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26195,f4247])).

fof(f26195,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16232,f4247])).

fof(f16232,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f4249])).

fof(f26194,plain,
    ( spl206_252
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26193,f8752,f25109])).

fof(f25109,plain,
    ( spl206_252
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_252])])).

fof(f26193,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26192,f4247])).

fof(f26192,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16233,f4247])).

fof(f16233,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f4249])).

fof(f26191,plain,
    ( spl206_251
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f26190,f8752,f25102])).

fof(f25102,plain,
    ( spl206_251
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_251])])).

fof(f26190,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f26189,f4247])).

fof(f26189,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16234,f4247])).

fof(f16234,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f4249])).

fof(f25916,plain,
    ( spl206_270
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25911,f8752,f25913])).

fof(f25913,plain,
    ( spl206_270
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_270])])).

fof(f25911,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25910,f4247])).

fof(f25910,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16371,f4247])).

fof(f16371,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)),k5_relat_1(k1_xboole_0,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4249])).

fof(f25895,plain,
    ( spl206_269
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25890,f8752,f25892])).

fof(f25890,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25889,f4247])).

fof(f25889,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16379,f4247])).

fof(f16379,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)),k5_relat_1(sK3,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4249])).

fof(f25876,plain,
    ( spl206_268
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25871,f8752,f25873])).

fof(f25873,plain,
    ( spl206_268
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)),k5_relat_1(sK89,k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_268])])).

fof(f25871,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)),k5_relat_1(sK89,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25870,f4247])).

fof(f25870,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)),k5_relat_1(sK89,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16386,f4247])).

fof(f16386,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)),k5_relat_1(sK89,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4249])).

fof(f25869,plain,
    ( spl206_267
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25864,f8752,f25866])).

fof(f25866,plain,
    ( spl206_267
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)),k5_relat_1(sK128,k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_267])])).

fof(f25864,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)),k5_relat_1(sK128,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25863,f4247])).

fof(f25863,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)),k5_relat_1(sK128,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16387,f4247])).

fof(f16387,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)),k5_relat_1(sK128,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4249])).

fof(f25862,plain,
    ( spl206_266
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25857,f8752,f25859])).

fof(f25859,plain,
    ( spl206_266
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)),k5_relat_1(sK162,k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_266])])).

fof(f25857,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)),k5_relat_1(sK162,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25856,f4247])).

fof(f25856,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)),k5_relat_1(sK162,k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16388,f4247])).

fof(f16388,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)),k5_relat_1(sK162,k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4249])).

fof(f25847,plain,
    ( spl206_265
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25842,f8752,f25844])).

fof(f25844,plain,
    ( spl206_265
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_265])])).

fof(f25842,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25841,f4247])).

fof(f25841,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16393,f4247])).

fof(f16393,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)),k5_relat_1(k1_xboole_0,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4249])).

fof(f25826,plain,
    ( spl206_264
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25821,f8752,f25823])).

fof(f25821,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25820,f4247])).

fof(f25820,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16401,f4247])).

fof(f16401,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)),k5_relat_1(sK3,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4249])).

fof(f25807,plain,
    ( spl206_263
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25802,f8752,f25804])).

fof(f25804,plain,
    ( spl206_263
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)),k5_relat_1(sK89,k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_263])])).

fof(f25802,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)),k5_relat_1(sK89,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25801,f4247])).

fof(f25801,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)),k5_relat_1(sK89,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16408,f4247])).

fof(f16408,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)),k5_relat_1(sK89,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4249])).

fof(f25800,plain,
    ( spl206_262
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25795,f8752,f25797])).

fof(f25797,plain,
    ( spl206_262
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)),k5_relat_1(sK128,k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_262])])).

fof(f25795,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)),k5_relat_1(sK128,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25794,f4247])).

fof(f25794,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)),k5_relat_1(sK128,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16409,f4247])).

fof(f16409,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)),k5_relat_1(sK128,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4249])).

fof(f25793,plain,
    ( spl206_261
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25788,f8752,f25790])).

fof(f25790,plain,
    ( spl206_261
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)),k5_relat_1(sK162,k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_261])])).

fof(f25788,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)),k5_relat_1(sK162,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25787,f4247])).

fof(f25787,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)),k5_relat_1(sK162,k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16410,f4247])).

fof(f16410,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)),k5_relat_1(sK162,k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4249])).

fof(f25778,plain,
    ( spl206_260
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25773,f8752,f25775])).

fof(f25775,plain,
    ( spl206_260
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_260])])).

fof(f25773,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25772,f4247])).

fof(f25772,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16415,f4247])).

fof(f16415,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)),k5_relat_1(k1_xboole_0,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4249])).

fof(f25757,plain,
    ( spl206_259
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25752,f8752,f25754])).

fof(f25752,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25751,f4247])).

fof(f25751,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16423,f4247])).

fof(f16423,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)),k5_relat_1(sK3,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4249])).

fof(f25738,plain,
    ( spl206_258
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25733,f8752,f25735])).

fof(f25735,plain,
    ( spl206_258
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)),k5_relat_1(sK89,k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_258])])).

fof(f25733,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)),k5_relat_1(sK89,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25732,f4247])).

fof(f25732,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)),k5_relat_1(sK89,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16430,f4247])).

fof(f16430,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)),k5_relat_1(sK89,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4249])).

fof(f25731,plain,
    ( spl206_257
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25726,f8752,f25728])).

fof(f25728,plain,
    ( spl206_257
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)),k5_relat_1(sK128,k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_257])])).

fof(f25726,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)),k5_relat_1(sK128,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25725,f4247])).

fof(f25725,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)),k5_relat_1(sK128,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16431,f4247])).

fof(f16431,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)),k5_relat_1(sK128,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4249])).

fof(f25724,plain,
    ( spl206_256
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25719,f8752,f25721])).

fof(f25721,plain,
    ( spl206_256
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)),k5_relat_1(sK162,k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_256])])).

fof(f25719,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)),k5_relat_1(sK162,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25718,f4247])).

fof(f25718,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)),k5_relat_1(sK162,k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16432,f4247])).

fof(f16432,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)),k5_relat_1(sK162,k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4249])).

fof(f25159,plain,
    ( spl206_255
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25154,f8752,f25156])).

fof(f25154,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25153,f4247])).

fof(f25153,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16701,f4247])).

fof(f16701,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f4249])).

fof(f25138,plain,
    ( spl206_254
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25133,f8752,f25135])).

fof(f25133,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25132,f4247])).

fof(f25132,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16709,f4247])).

fof(f16709,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f8754,f4249])).

fof(f25119,plain,
    ( spl206_253
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25114,f8752,f25116])).

fof(f25114,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25113,f4247])).

fof(f25113,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16716,f4247])).

fof(f16716,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f4249])).

fof(f25112,plain,
    ( spl206_252
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25107,f8752,f25109])).

fof(f25107,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25106,f4247])).

fof(f25106,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16717,f4247])).

fof(f16717,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f4249])).

fof(f25105,plain,
    ( spl206_251
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f25100,f8752,f25102])).

fof(f25100,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f25099,f4247])).

fof(f25099,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16718,f4247])).

fof(f16718,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f4249])).

fof(f24826,plain,
    ( spl206_250
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24821,f8752,f24823])).

fof(f24823,plain,
    ( spl206_250
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_250])])).

fof(f24821,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24820,f4247])).

fof(f24820,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16855,f4247])).

fof(f16855,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4249])).

fof(f24805,plain,
    ( spl206_249
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24800,f8752,f24802])).

fof(f24800,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24799,f4247])).

fof(f24799,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16863,f4247])).

fof(f16863,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4249])).

fof(f24786,plain,
    ( spl206_248
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24781,f8752,f24783])).

fof(f24783,plain,
    ( spl206_248
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_248])])).

fof(f24781,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24780,f4247])).

fof(f24780,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16870,f4247])).

fof(f16870,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4249])).

fof(f24779,plain,
    ( spl206_247
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24774,f8752,f24776])).

fof(f24776,plain,
    ( spl206_247
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_247])])).

fof(f24774,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24773,f4247])).

fof(f24773,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16871,f4247])).

fof(f16871,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4249])).

fof(f24772,plain,
    ( spl206_246
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24767,f8752,f24769])).

fof(f24769,plain,
    ( spl206_246
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_246])])).

fof(f24767,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24766,f4247])).

fof(f24766,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16872,f4247])).

fof(f16872,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4249])).

fof(f24757,plain,
    ( spl206_245
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24752,f8752,f24754])).

fof(f24754,plain,
    ( spl206_245
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_245])])).

fof(f24752,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24751,f4247])).

fof(f24751,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16877,f4247])).

fof(f16877,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4249])).

fof(f24736,plain,
    ( spl206_244
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24731,f8752,f24733])).

fof(f24731,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24730,f4247])).

fof(f24730,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16885,f4247])).

fof(f16885,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4249])).

fof(f24717,plain,
    ( spl206_243
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24712,f8752,f24714])).

fof(f24714,plain,
    ( spl206_243
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_243])])).

fof(f24712,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24711,f4247])).

fof(f24711,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16892,f4247])).

fof(f16892,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4249])).

fof(f24710,plain,
    ( spl206_242
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24705,f8752,f24707])).

fof(f24707,plain,
    ( spl206_242
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_242])])).

fof(f24705,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24704,f4247])).

fof(f24704,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16893,f4247])).

fof(f16893,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4249])).

fof(f24703,plain,
    ( spl206_241
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24698,f8752,f24700])).

fof(f24700,plain,
    ( spl206_241
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_241])])).

fof(f24698,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24697,f4247])).

fof(f24697,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16894,f4247])).

fof(f16894,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4249])).

fof(f24688,plain,
    ( spl206_240
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24683,f8752,f24685])).

fof(f24685,plain,
    ( spl206_240
  <=> r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_240])])).

fof(f24683,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24682,f4247])).

fof(f24682,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16899,f4247])).

fof(f16899,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3)),k5_relat_1(k1_xboole_0,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4249])).

fof(f24667,plain,
    ( spl206_239
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24662,f8752,f24664])).

fof(f24662,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24661,f4247])).

fof(f24661,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16907,f4247])).

fof(f16907,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)),k5_relat_1(sK3,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4249])).

fof(f24648,plain,
    ( spl206_238
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24643,f8752,f24645])).

fof(f24645,plain,
    ( spl206_238
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_238])])).

fof(f24643,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24642,f4247])).

fof(f24642,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16914,f4247])).

fof(f16914,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3)),k5_relat_1(sK89,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4249])).

fof(f24641,plain,
    ( spl206_237
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24636,f8752,f24638])).

fof(f24638,plain,
    ( spl206_237
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_237])])).

fof(f24636,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24635,f4247])).

fof(f24635,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16915,f4247])).

fof(f16915,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3)),k5_relat_1(sK128,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4249])).

fof(f24634,plain,
    ( spl206_236
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24629,f8752,f24631])).

fof(f24631,plain,
    ( spl206_236
  <=> r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_236])])).

fof(f24629,plain,
    ( r1_tarski(k4_xboole_0(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24628,f4247])).

fof(f24628,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f16916,f4247])).

fof(f16916,plain,
    ( r1_tarski(k6_subset_1(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3)),k5_relat_1(sK162,k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4249])).

fof(f24422,plain,
    ( spl206_232
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24421,f8752,f24344])).

fof(f24344,plain,
    ( spl206_232
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_232])])).

fof(f24421,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24420,f4247])).

fof(f24420,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17017,f4247])).

fof(f17017,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4250])).

fof(f4250,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2158])).

fof(f2158,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f763])).

fof(f763,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k1_relat_1(X0),k1_relat_1(X1)),k1_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_relat_1)).

fof(f24398,plain,
    ( spl206_235
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24393,f8752,f24395])).

fof(f24395,plain,
    ( spl206_235
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89)),k1_relat_1(k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_235])])).

fof(f24393,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89)),k1_relat_1(k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24392,f4247])).

fof(f24392,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK89)),k1_relat_1(k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17024,f4247])).

fof(f17024,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK89)),k1_relat_1(k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4250])).

fof(f24391,plain,
    ( spl206_234
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24386,f8752,f24388])).

fof(f24388,plain,
    ( spl206_234
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128)),k1_relat_1(k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_234])])).

fof(f24386,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128)),k1_relat_1(k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24385,f4247])).

fof(f24385,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK128)),k1_relat_1(k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17025,f4247])).

fof(f17025,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK128)),k1_relat_1(k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4250])).

fof(f24384,plain,
    ( spl206_233
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24379,f8752,f24381])).

fof(f24381,plain,
    ( spl206_233
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162)),k1_relat_1(k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_233])])).

fof(f24379,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162)),k1_relat_1(k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24378,f4247])).

fof(f24378,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK162)),k1_relat_1(k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17026,f4247])).

fof(f17026,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK162)),k1_relat_1(k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4250])).

fof(f24347,plain,
    ( spl206_232
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24342,f8752,f24344])).

fof(f24342,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24341,f4247])).

fof(f24341,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17039,f4247])).

fof(f17039,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK3),k1_relat_1(sK3)),k1_relat_1(k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4250])).

fof(f24319,plain,
    ( spl206_231
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24314,f8752,f24316])).

fof(f24316,plain,
    ( spl206_231
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK89),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_231])])).

fof(f24314,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK89),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24313,f4247])).

fof(f24313,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK89),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17046,f4247])).

fof(f17046,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK89),k1_relat_1(sK3)),k1_relat_1(k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4250])).

fof(f24312,plain,
    ( spl206_230
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24307,f8752,f24309])).

fof(f24309,plain,
    ( spl206_230
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK128),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_230])])).

fof(f24307,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK128),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24306,f4247])).

fof(f24306,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK128),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17047,f4247])).

fof(f17047,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK128),k1_relat_1(sK3)),k1_relat_1(k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4250])).

fof(f24305,plain,
    ( spl206_229
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24300,f8752,f24302])).

fof(f24302,plain,
    ( spl206_229
  <=> r1_tarski(k4_xboole_0(k1_relat_1(sK162),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_229])])).

fof(f24300,plain,
    ( r1_tarski(k4_xboole_0(k1_relat_1(sK162),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24299,f4247])).

fof(f24299,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK162),k1_relat_1(sK3)),k1_relat_1(k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17048,f4247])).

fof(f17048,plain,
    ( r1_tarski(k6_subset_1(k1_relat_1(sK162),k1_relat_1(sK3)),k1_relat_1(k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4250])).

fof(f24269,plain,
    ( spl206_225
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24268,f8752,f24200])).

fof(f24200,plain,
    ( spl206_225
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_225])])).

fof(f24268,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24267,f4247])).

fof(f24267,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17061,f4247])).

fof(f17061,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4251])).

fof(f4251,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2159])).

fof(f2159,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f832])).

fof(f832,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k6_subset_1(k2_relat_1(X0),k2_relat_1(X1)),k2_relat_1(k6_subset_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relat_1)).

fof(f24254,plain,
    ( spl206_228
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24249,f8752,f24251])).

fof(f24251,plain,
    ( spl206_228
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89)),k2_relat_1(k4_xboole_0(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_228])])).

fof(f24249,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89)),k2_relat_1(k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24248,f4247])).

fof(f24248,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK89)),k2_relat_1(k4_xboole_0(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17068,f4247])).

fof(f17068,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK89)),k2_relat_1(k6_subset_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4251])).

fof(f24247,plain,
    ( spl206_227
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24242,f8752,f24244])).

fof(f24244,plain,
    ( spl206_227
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128)),k2_relat_1(k4_xboole_0(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_227])])).

fof(f24242,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128)),k2_relat_1(k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24241,f4247])).

fof(f24241,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK128)),k2_relat_1(k4_xboole_0(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17069,f4247])).

fof(f17069,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK128)),k2_relat_1(k6_subset_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4251])).

fof(f24240,plain,
    ( spl206_226
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24235,f8752,f24237])).

fof(f24237,plain,
    ( spl206_226
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162)),k2_relat_1(k4_xboole_0(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_226])])).

fof(f24235,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162)),k2_relat_1(k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24234,f4247])).

fof(f24234,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK162)),k2_relat_1(k4_xboole_0(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17070,f4247])).

fof(f17070,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK162)),k2_relat_1(k6_subset_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4251])).

fof(f24203,plain,
    ( spl206_225
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24198,f8752,f24200])).

fof(f24198,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24197,f4247])).

fof(f24197,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17083,f4247])).

fof(f17083,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK3),k2_relat_1(sK3)),k2_relat_1(k6_subset_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f8754,f4251])).

fof(f24184,plain,
    ( spl206_224
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24179,f8752,f24181])).

fof(f24181,plain,
    ( spl206_224
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK89),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_224])])).

fof(f24179,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK89),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24178,f4247])).

fof(f24178,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK89),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17090,f4247])).

fof(f17090,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK89),k2_relat_1(sK3)),k2_relat_1(k6_subset_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4251])).

fof(f24177,plain,
    ( spl206_223
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24172,f8752,f24174])).

fof(f24174,plain,
    ( spl206_223
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK128),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_223])])).

fof(f24172,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK128),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24171,f4247])).

fof(f24171,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK128),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17091,f4247])).

fof(f17091,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK128),k2_relat_1(sK3)),k2_relat_1(k6_subset_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4251])).

fof(f24170,plain,
    ( spl206_222
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24165,f8752,f24167])).

fof(f24167,plain,
    ( spl206_222
  <=> r1_tarski(k4_xboole_0(k2_relat_1(sK162),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_222])])).

fof(f24165,plain,
    ( r1_tarski(k4_xboole_0(k2_relat_1(sK162),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24164,f4247])).

fof(f24164,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK162),k2_relat_1(sK3)),k2_relat_1(k4_xboole_0(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17092,f4247])).

fof(f17092,plain,
    ( r1_tarski(k6_subset_1(k2_relat_1(sK162),k2_relat_1(sK3)),k2_relat_1(k6_subset_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4251])).

fof(f24155,plain,
    ( spl206_221
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17097,f8752,f24150])).

fof(f17097,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4299,f8754,f4258])).

fof(f24154,plain,
    ( spl206_221
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17098,f8752,f24150])).

fof(f17098,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4289,f8754,f4258])).

fof(f24153,plain,
    ( spl206_221
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17099,f8752,f24150])).

fof(f17099,plain,
    ( v1_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4287,f8754,f4258])).

fof(f24148,plain,
    ( spl206_220
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17117,f8752,f24144])).

fof(f24144,plain,
    ( spl206_220
  <=> v5_relat_1(sK3,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_220])])).

fof(f17117,plain,
    ( v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f4285])).

fof(f4285,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2741])).

fof(f24147,plain,
    ( spl206_220
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17118,f8752,f24144])).

fof(f17118,plain,
    ( v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f4285])).

fof(f24142,plain,
    ( spl206_219
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17119,f8752,f24139])).

fof(f24139,plain,
    ( spl206_219
  <=> v5_relat_1(sK3,k1_zfmisc_1(k3_tarski(k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_219])])).

fof(f17119,plain,
    ( v5_relat_1(sK3,k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f4285])).

fof(f24137,plain,
    ( spl206_218
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17121,f8752,f24133])).

fof(f17121,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4288,f8754,f4305])).

fof(f24136,plain,
    ( spl206_218
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17122,f8752,f24133])).

fof(f17122,plain,
    ( v1_relat_1(k5_relat_1(k1_xboole_0,sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4286,f8754,f4305])).

fof(f24131,plain,
    ( spl206_217
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17141,f8752,f24127])).

fof(f24127,plain,
    ( spl206_217
  <=> v4_relat_1(sK3,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_217])])).

fof(f17141,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4882,f8754,f4313])).

fof(f4313,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2744])).

fof(f24130,plain,
    ( spl206_217
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17142,f8752,f24127])).

fof(f17142,plain,
    ( v4_relat_1(sK3,k1_relat_1(sK3))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4881,f8754,f4313])).

fof(f24125,plain,
    ( spl206_216
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17143,f8752,f24122])).

fof(f24122,plain,
    ( spl206_216
  <=> v4_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_216])])).

fof(f17143,plain,
    ( v4_relat_1(sK3,k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4083,f8754,f4313])).

fof(f24096,plain,
    ( spl206_215
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17160,f8752,f24042])).

fof(f24042,plain,
    ( spl206_215
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_215])])).

fof(f17160,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4367])).

fof(f4367,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k1_relat_1(X0),k4_xboole_0(k1_relat_1(X0),k1_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2827,f3248,f3248])).

fof(f2827,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1315])).

fof(f1315,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f752])).

fof(f752,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k1_relat_1(X0),k1_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relat_1)).

fof(f24095,plain,
    ( spl206_214
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17161,f8752,f24035])).

fof(f24035,plain,
    ( spl206_214
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_214])])).

fof(f17161,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4367])).

fof(f24094,plain,
    ( spl206_213
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17162,f8752,f24028])).

fof(f24028,plain,
    ( spl206_213
  <=> r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_213])])).

fof(f17162,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4367])).

fof(f24045,plain,
    ( spl206_215
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24040,f8752,f24042])).

fof(f24040,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24039,f4596])).

fof(f4596,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f3254,f3248,f3248])).

fof(f3254,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f24039,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17182,f4596])).

fof(f17182,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k1_relat_1(sK89),k4_xboole_0(k1_relat_1(sK89),k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4367])).

fof(f24038,plain,
    ( spl206_214
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24033,f8752,f24035])).

fof(f24033,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24032,f4596])).

fof(f24032,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17183,f4596])).

fof(f17183,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k1_relat_1(sK128),k4_xboole_0(k1_relat_1(sK128),k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4367])).

fof(f24031,plain,
    ( spl206_213
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f24026,f8752,f24028])).

fof(f24026,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f24025,f4596])).

fof(f24025,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k1_relat_1(sK3),k4_xboole_0(k1_relat_1(sK3),k1_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17184,f4596])).

fof(f17184,plain,
    ( r1_tarski(k1_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k1_relat_1(sK162),k4_xboole_0(k1_relat_1(sK162),k1_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4367])).

fof(f24004,plain,
    ( spl206_212
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17204,f8752,f23962])).

fof(f23962,plain,
    ( spl206_212
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_212])])).

fof(f17204,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4368])).

fof(f4368,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k2_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k2_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2828,f3248,f3248])).

fof(f2828,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1316])).

fof(f1316,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f831])).

fof(f831,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f24003,plain,
    ( spl206_211
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17205,f8752,f23955])).

fof(f23955,plain,
    ( spl206_211
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_211])])).

fof(f17205,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4368])).

fof(f24002,plain,
    ( spl206_210
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17206,f8752,f23948])).

fof(f23948,plain,
    ( spl206_210
  <=> r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_210])])).

fof(f17206,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4368])).

fof(f23965,plain,
    ( spl206_212
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23960,f8752,f23962])).

fof(f23960,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23959,f4596])).

fof(f23959,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17226,f4596])).

fof(f17226,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k2_relat_1(sK89),k4_xboole_0(k2_relat_1(sK89),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4368])).

fof(f23958,plain,
    ( spl206_211
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23953,f8752,f23955])).

fof(f23953,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23952,f4596])).

fof(f23952,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17227,f4596])).

fof(f17227,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k2_relat_1(sK128),k4_xboole_0(k2_relat_1(sK128),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4368])).

fof(f23951,plain,
    ( spl206_210
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23946,f8752,f23948])).

fof(f23946,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23945,f4596])).

fof(f23945,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k2_relat_1(sK3),k4_xboole_0(k2_relat_1(sK3),k2_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17228,f4596])).

fof(f17228,plain,
    ( r1_tarski(k2_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k2_relat_1(sK162),k4_xboole_0(k2_relat_1(sK162),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4368])).

fof(f23936,plain,
    ( spl206_209
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17235,f8752,f23933])).

fof(f23933,plain,
    ( spl206_209
  <=> sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_209])])).

fof(f17235,plain,
    ( sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4415])).

fof(f4415,plain,(
    ! [X0] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f2975,f3248])).

fof(f2975,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1399])).

fof(f1399,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f826])).

fof(f826,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

fof(f23931,plain,
    ( spl206_208
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17242,f8752,f23928])).

fof(f23928,plain,
    ( spl206_208
  <=> k1_xboole_0 = k10_relat_1(sK3,k2_tarski(sK177(k2_relat_1(sK3)),sK177(k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_208])])).

fof(f17242,plain,
    ( k1_xboole_0 = k10_relat_1(sK3,k2_tarski(sK177(k2_relat_1(sK3)),sK177(k2_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4021,f8754,f4527])).

fof(f4527,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k2_tarski(X0,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f3175,f3202])).

fof(f3175,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_relat_1(X1))
      | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f2351])).

fof(f2351,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k2_relat_1(X1))
          | k1_xboole_0 = k10_relat_1(X1,k1_tarski(X0)) )
        & ( k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0))
          | ~ r2_hidden(X0,k2_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f1550])).

fof(f1550,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f961])).

fof(f961,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k2_relat_1(X1))
      <=> k1_xboole_0 != k10_relat_1(X1,k1_tarski(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_1)).

fof(f23917,plain,
    ( spl206_200
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23916,f8752,f23494])).

fof(f23494,plain,
    ( spl206_200
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_200])])).

fof(f23916,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17260,f3489])).

fof(f17260,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4599])).

fof(f4599,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))),k4_xboole_0(k5_relat_1(X0,X1),k4_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3257,f3248,f3248])).

fof(f3257,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1593])).

fof(f1593,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f851])).

fof(f851,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => r1_tarski(k5_relat_1(X0,k3_xboole_0(X1,X2)),k3_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_relat_1)).

fof(f23909,plain,
    ( spl206_207
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23908,f8752,f23744])).

fof(f23744,plain,
    ( spl206_207
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_207])])).

fof(f23908,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17267,f3489])).

fof(f17267,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK89))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4599])).

fof(f23907,plain,
    ( spl206_206
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23906,f8752,f23729])).

fof(f23729,plain,
    ( spl206_206
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_206])])).

fof(f23906,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17268,f3489])).

fof(f17268,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK128))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4599])).

fof(f23905,plain,
    ( spl206_204
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23904,f8752,f23708])).

fof(f23708,plain,
    ( spl206_204
  <=> r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_204])])).

fof(f23904,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17269,f3489])).

fof(f17269,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK162))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4599])).

fof(f23822,plain,
    ( spl206_200
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23821,f8752,f23494])).

fof(f23821,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23820,f3489])).

fof(f23820,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23819,f4596])).

fof(f23819,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17428,f4596])).

fof(f17428,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f4599])).

fof(f23816,plain,
    ( spl206_195
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17443,f8752,f22823])).

fof(f22823,plain,
    ( spl206_195
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_195])])).

fof(f17443,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f4599])).

fof(f23815,plain,
    ( spl206_190
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17444,f8752,f22754])).

fof(f22754,plain,
    ( spl206_190
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_190])])).

fof(f17444,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f4599])).

fof(f23814,plain,
    ( spl206_185
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17445,f8752,f22685])).

fof(f22685,plain,
    ( spl206_185
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_185])])).

fof(f17445,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f4599])).

fof(f23747,plain,
    ( spl206_207
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23742,f8752,f23744])).

fof(f23742,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23741,f3489])).

fof(f23741,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK89))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23740,f4596])).

fof(f23740,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17582,f4596])).

fof(f17582,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4599])).

fof(f23739,plain,
    ( spl206_195
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23738,f8752,f22823])).

fof(f23738,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23737,f4596])).

fof(f23737,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17590,f4596])).

fof(f17590,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4599])).

fof(f23734,plain,
    ( spl206_205
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17598,f8752,f23718])).

fof(f23718,plain,
    ( spl206_205
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK128))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_205])])).

fof(f17598,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK128))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4599])).

fof(f23733,plain,
    ( spl206_203
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17599,f8752,f23697])).

fof(f23697,plain,
    ( spl206_203
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK162))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_203])])).

fof(f17599,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK162))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4599])).

fof(f23732,plain,
    ( spl206_206
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23727,f8752,f23729])).

fof(f23727,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23726,f3489])).

fof(f23726,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK128))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23725,f4596])).

fof(f23725,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17604,f4596])).

fof(f17604,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4599])).

fof(f23724,plain,
    ( spl206_190
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23723,f8752,f22754])).

fof(f23723,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23722,f4596])).

fof(f23722,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17612,f4596])).

fof(f17612,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4599])).

fof(f23721,plain,
    ( spl206_205
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23716,f8752,f23718])).

fof(f23716,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK128))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23715,f4596])).

fof(f23715,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK89))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17619,f4596])).

fof(f17619,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK89))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4599])).

fof(f23712,plain,
    ( spl206_202
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f17621,f8752,f23690])).

fof(f23690,plain,
    ( spl206_202
  <=> r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK162))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_202])])).

fof(f17621,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK162))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4599])).

fof(f23711,plain,
    ( spl206_204
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23706,f8752,f23708])).

fof(f23706,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23705,f3489])).

fof(f23705,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK162))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23704,f4596])).

fof(f23704,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17626,f4596])).

fof(f17626,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,sK162),k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4599])).

fof(f23703,plain,
    ( spl206_185
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23702,f8752,f22685])).

fof(f23702,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23701,f4596])).

fof(f23701,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17634,f4596])).

fof(f17634,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK3,sK162),k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4599])).

fof(f23700,plain,
    ( spl206_203
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23695,f8752,f23697])).

fof(f23695,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK162))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23694,f4596])).

fof(f23694,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK89))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17641,f4596])).

fof(f17641,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK89))),k4_xboole_0(k5_relat_1(sK3,sK162),k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4599])).

fof(f23693,plain,
    ( spl206_202
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23688,f8752,f23690])).

fof(f23688,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK162))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23687,f4596])).

fof(f23687,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK128))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17642,f4596])).

fof(f17642,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK128))),k4_xboole_0(k5_relat_1(sK3,sK162),k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4599])).

fof(f23640,plain,
    ( spl206_201
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23639,f8752,f23507])).

fof(f23507,plain,
    ( spl206_201
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_201])])).

fof(f23639,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23638,f3489])).

fof(f23638,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23637,f4596])).

fof(f23637,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17736,f4596])).

fof(f17736,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f4599])).

fof(f23615,plain,
    ( spl206_200
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23614,f8752,f23494])).

fof(f23614,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23613,f3489])).

fof(f23613,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23612,f4596])).

fof(f23612,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17744,f4596])).

fof(f17744,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4599])).

fof(f23593,plain,
    ( spl206_199
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23592,f8752,f23482])).

fof(f23482,plain,
    ( spl206_199
  <=> r1_tarski(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_199])])).

fof(f23592,plain,
    ( r1_tarski(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23591,f3489])).

fof(f23591,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23590,f4596])).

fof(f23590,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17751,f4596])).

fof(f17751,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4599])).

fof(f23589,plain,
    ( spl206_198
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23588,f8752,f23476])).

fof(f23476,plain,
    ( spl206_198
  <=> r1_tarski(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_198])])).

fof(f23588,plain,
    ( r1_tarski(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23587,f3489])).

fof(f23587,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23586,f4596])).

fof(f23586,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17752,f4596])).

fof(f17752,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4599])).

fof(f23585,plain,
    ( spl206_197
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23584,f8752,f23470])).

fof(f23470,plain,
    ( spl206_197
  <=> r1_tarski(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_197])])).

fof(f23584,plain,
    ( r1_tarski(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23583,f3489])).

fof(f23583,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f23582,f4596])).

fof(f23582,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f17753,f4596])).

fof(f17753,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,k1_xboole_0))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,k1_xboole_0))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4599])).

fof(f23525,plain,
    ( spl206_196
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18066,f8752,f22844])).

fof(f22844,plain,
    ( spl206_196
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_196])])).

fof(f18066,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4599])).

fof(f23524,plain,
    ( spl206_195
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18074,f8752,f22823])).

fof(f18074,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4599])).

fof(f23523,plain,
    ( spl206_194
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18081,f8752,f22804])).

fof(f22804,plain,
    ( spl206_194
  <=> r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_194])])).

fof(f18081,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4599])).

fof(f23522,plain,
    ( spl206_193
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18082,f8752,f22797])).

fof(f22797,plain,
    ( spl206_193
  <=> r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_193])])).

fof(f18082,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4599])).

fof(f23521,plain,
    ( spl206_192
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18083,f8752,f22790])).

fof(f22790,plain,
    ( spl206_192
  <=> r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_192])])).

fof(f18083,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4599])).

fof(f23520,plain,
    ( spl206_191
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18088,f8752,f22775])).

fof(f22775,plain,
    ( spl206_191
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_191])])).

fof(f18088,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4599])).

fof(f23519,plain,
    ( spl206_190
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18096,f8752,f22754])).

fof(f18096,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4599])).

fof(f23518,plain,
    ( spl206_189
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18103,f8752,f22735])).

fof(f22735,plain,
    ( spl206_189
  <=> r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_189])])).

fof(f18103,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4599])).

fof(f23517,plain,
    ( spl206_188
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18104,f8752,f22728])).

fof(f22728,plain,
    ( spl206_188
  <=> r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_188])])).

fof(f18104,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4599])).

fof(f23516,plain,
    ( spl206_187
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18105,f8752,f22721])).

fof(f22721,plain,
    ( spl206_187
  <=> r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_187])])).

fof(f18105,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4599])).

fof(f23515,plain,
    ( spl206_186
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18110,f8752,f22706])).

fof(f22706,plain,
    ( spl206_186
  <=> r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_186])])).

fof(f18110,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4599])).

fof(f23514,plain,
    ( spl206_185
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18118,f8752,f22685])).

fof(f18118,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4599])).

fof(f23513,plain,
    ( spl206_184
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18125,f8752,f22666])).

fof(f22666,plain,
    ( spl206_184
  <=> r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_184])])).

fof(f18125,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4599])).

fof(f23512,plain,
    ( spl206_183
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18126,f8752,f22659])).

fof(f22659,plain,
    ( spl206_183
  <=> r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_183])])).

fof(f18126,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4599])).

fof(f23511,plain,
    ( spl206_182
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18127,f8752,f22652])).

fof(f22652,plain,
    ( spl206_182
  <=> r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_182])])).

fof(f18127,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4599])).

fof(f23510,plain,
    ( spl206_201
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23505,f8752,f23507])).

fof(f23505,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18220,f3489])).

fof(f18220,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k4_xboole_0(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f4599])).

fof(f23497,plain,
    ( spl206_200
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23492,f8752,f23494])).

fof(f23492,plain,
    ( r1_tarski(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18228,f3489])).

fof(f18228,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k4_xboole_0(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4599])).

fof(f23485,plain,
    ( spl206_199
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23480,f8752,f23482])).

fof(f23480,plain,
    ( r1_tarski(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18235,f3489])).

fof(f18235,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k4_xboole_0(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4599])).

fof(f23479,plain,
    ( spl206_198
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23474,f8752,f23476])).

fof(f23474,plain,
    ( r1_tarski(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18236,f3489])).

fof(f18236,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k4_xboole_0(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4599])).

fof(f23473,plain,
    ( spl206_197
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f23468,f8752,f23470])).

fof(f23468,plain,
    ( r1_tarski(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18237,f3489])).

fof(f18237,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK3))),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k4_xboole_0(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4599])).

fof(f22847,plain,
    ( spl206_196
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22842,f8752,f22844])).

fof(f22842,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22841,f4596])).

fof(f22841,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18550,f4596])).

fof(f18550,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK89),k4_xboole_0(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4599])).

fof(f22826,plain,
    ( spl206_195
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22821,f8752,f22823])).

fof(f22821,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22820,f4596])).

fof(f22820,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18558,f4596])).

fof(f18558,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK3,sK89),k4_xboole_0(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4599])).

fof(f22807,plain,
    ( spl206_194
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22802,f8752,f22804])).

fof(f22802,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22801,f4596])).

fof(f22801,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18565,f4596])).

fof(f18565,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK89,sK89),k4_xboole_0(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4599])).

fof(f22800,plain,
    ( spl206_193
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22795,f8752,f22797])).

fof(f22795,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22794,f4596])).

fof(f22794,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18566,f4596])).

fof(f18566,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK128,sK89),k4_xboole_0(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4599])).

fof(f22793,plain,
    ( spl206_192
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22788,f8752,f22790])).

fof(f22788,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22787,f4596])).

fof(f22787,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18567,f4596])).

fof(f18567,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k5_relat_1(sK162,sK89),k4_xboole_0(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4599])).

fof(f22778,plain,
    ( spl206_191
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22773,f8752,f22775])).

fof(f22773,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22772,f4596])).

fof(f22772,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18572,f4596])).

fof(f18572,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK128),k4_xboole_0(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4599])).

fof(f22757,plain,
    ( spl206_190
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22752,f8752,f22754])).

fof(f22752,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22751,f4596])).

fof(f22751,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18580,f4596])).

fof(f18580,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK3,sK128),k4_xboole_0(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4599])).

fof(f22738,plain,
    ( spl206_189
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22733,f8752,f22735])).

fof(f22733,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22732,f4596])).

fof(f22732,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18587,f4596])).

fof(f18587,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK89,sK128),k4_xboole_0(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4599])).

fof(f22731,plain,
    ( spl206_188
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22726,f8752,f22728])).

fof(f22726,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22725,f4596])).

fof(f22725,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18588,f4596])).

fof(f18588,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK128,sK128),k4_xboole_0(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4599])).

fof(f22724,plain,
    ( spl206_187
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22719,f8752,f22721])).

fof(f22719,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22718,f4596])).

fof(f22718,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18589,f4596])).

fof(f18589,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k5_relat_1(sK162,sK128),k4_xboole_0(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4599])).

fof(f22709,plain,
    ( spl206_186
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22704,f8752,f22706])).

fof(f22704,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22703,f4596])).

fof(f22703,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k4_xboole_0(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18594,f4596])).

fof(f18594,plain,
    ( r1_tarski(k5_relat_1(k1_xboole_0,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(k1_xboole_0,sK162),k4_xboole_0(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4599])).

fof(f22688,plain,
    ( spl206_185
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22683,f8752,f22685])).

fof(f22683,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22682,f4596])).

fof(f22682,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK3,sK3),k4_xboole_0(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18602,f4596])).

fof(f18602,plain,
    ( r1_tarski(k5_relat_1(sK3,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK3,sK162),k4_xboole_0(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4599])).

fof(f22669,plain,
    ( spl206_184
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22664,f8752,f22666])).

fof(f22664,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22663,f4596])).

fof(f22663,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK89,sK3),k4_xboole_0(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18609,f4596])).

fof(f18609,plain,
    ( r1_tarski(k5_relat_1(sK89,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK89,sK162),k4_xboole_0(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4599])).

fof(f22662,plain,
    ( spl206_183
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22657,f8752,f22659])).

fof(f22657,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22656,f4596])).

fof(f22656,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK128,sK3),k4_xboole_0(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18610,f4596])).

fof(f18610,plain,
    ( r1_tarski(k5_relat_1(sK128,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK128,sK162),k4_xboole_0(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4599])).

fof(f22655,plain,
    ( spl206_182
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22650,f8752,f22652])).

fof(f22650,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22649,f4596])).

fof(f22649,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK162,sK3),k4_xboole_0(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18611,f4596])).

fof(f18611,plain,
    ( r1_tarski(k5_relat_1(sK162,k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k5_relat_1(sK162,sK162),k4_xboole_0(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4599])).

fof(f22455,plain,
    ( spl206_181
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18719,f8752,f22416])).

fof(f22416,plain,
    ( spl206_181
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK89)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_181])])).

fof(f18719,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4600])).

fof(f4600,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))),k4_xboole_0(k3_relat_1(X0),k4_xboole_0(k3_relat_1(X0),k3_relat_1(X1))))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3258,f3248,f3248])).

fof(f3258,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1594])).

fof(f1594,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f837])).

fof(f837,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relat_1)).

fof(f22454,plain,
    ( spl206_180
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18720,f8752,f22409])).

fof(f22409,plain,
    ( spl206_180
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK128)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_180])])).

fof(f18720,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4600])).

fof(f22453,plain,
    ( spl206_179
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18721,f8752,f22402])).

fof(f22402,plain,
    ( spl206_179
  <=> r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK162)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_179])])).

fof(f18721,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4600])).

fof(f22419,plain,
    ( spl206_181
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22414,f8752,f22416])).

fof(f22414,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22413,f4596])).

fof(f22413,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK89))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18741,f4596])).

fof(f18741,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))),k4_xboole_0(k3_relat_1(sK89),k4_xboole_0(k3_relat_1(sK89),k3_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4600])).

fof(f22412,plain,
    ( spl206_180
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22407,f8752,f22409])).

fof(f22407,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22406,f4596])).

fof(f22406,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK128))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18742,f4596])).

fof(f18742,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))),k4_xboole_0(k3_relat_1(sK128),k4_xboole_0(k3_relat_1(sK128),k3_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4600])).

fof(f22405,plain,
    ( spl206_179
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22400,f8752,f22402])).

fof(f22400,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22399,f4596])).

fof(f22399,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k3_relat_1(sK3),k4_xboole_0(k3_relat_1(sK3),k3_relat_1(sK162))))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18743,f4596])).

fof(f18743,plain,
    ( r1_tarski(k3_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))),k4_xboole_0(k3_relat_1(sK162),k4_xboole_0(k3_relat_1(sK162),k3_relat_1(sK3))))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4600])).

fof(f22390,plain,
    ( spl206_178
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22389,f8752,f22381])).

fof(f22381,plain,
    ( spl206_178
  <=> v1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_178])])).

fof(f22389,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18749,f4635])).

fof(f18749,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4626])).

fof(f4626,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_tarski(k2_tarski(X0,X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3284,f3631])).

fof(f3284,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1614])).

fof(f1614,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1613])).

fof(f1613,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_xboole_0(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f694])).

fof(f694,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_relat_1)).

fof(f22387,plain,
    ( spl206_177
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18764,f8752,f22362])).

fof(f22362,plain,
    ( spl206_177
  <=> v1_relat_1(k3_tarski(k2_tarski(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_177])])).

fof(f18764,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4626])).

fof(f22386,plain,
    ( spl206_176
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18765,f8752,f22356])).

fof(f22356,plain,
    ( spl206_176
  <=> v1_relat_1(k3_tarski(k2_tarski(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_176])])).

fof(f18765,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4626])).

fof(f22385,plain,
    ( spl206_175
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18766,f8752,f22350])).

fof(f22350,plain,
    ( spl206_175
  <=> v1_relat_1(k3_tarski(k2_tarski(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_175])])).

fof(f18766,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4626])).

fof(f22384,plain,
    ( spl206_178
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18771,f8752,f22381])).

fof(f18771,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4626])).

fof(f22365,plain,
    ( spl206_177
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22360,f8752,f22362])).

fof(f22360,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18786,f4635])).

fof(f18786,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4626])).

fof(f22359,plain,
    ( spl206_176
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22354,f8752,f22356])).

fof(f22354,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18787,f4635])).

fof(f18787,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4626])).

fof(f22353,plain,
    ( spl206_175
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22348,f8752,f22350])).

fof(f22348,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18788,f4635])).

fof(f18788,plain,
    ( v1_relat_1(k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4626])).

fof(f22340,plain,
    ( spl206_167
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18801,f8752,f22005])).

fof(f22005,plain,
    ( spl206_167
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_167])])).

fof(f18801,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4638])).

fof(f4638,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k3_tarski(k2_tarski(X1,X2))) = k3_tarski(k2_tarski(k5_relat_1(X0,X1),k5_relat_1(X0,X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3296,f3631,f3631])).

fof(f3296,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1620])).

fof(f1620,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f850])).

fof(f850,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k5_relat_1(X0,X1),k5_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_relat_1)).

fof(f22339,plain,
    ( spl206_174
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18808,f8752,f22193])).

fof(f22193,plain,
    ( spl206_174
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_174])])).

fof(f18808,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4638])).

fof(f22338,plain,
    ( spl206_173
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18809,f8752,f22180])).

fof(f22180,plain,
    ( spl206_173
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_173])])).

fof(f18809,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4638])).

fof(f22337,plain,
    ( spl206_171
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18810,f8752,f22161])).

fof(f22161,plain,
    ( spl206_171
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_171])])).

fof(f18810,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4638])).

fof(f22263,plain,
    ( spl206_167
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22262,f8752,f22005])).

fof(f22262,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22261,f4635])).

fof(f22261,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f18969,f3634])).

fof(f18969,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f8754,f4638])).

fof(f22259,plain,
    ( spl206_162
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18984,f8752,f21370])).

fof(f21370,plain,
    ( spl206_162
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_162])])).

fof(f18984,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f8754,f4638])).

fof(f22258,plain,
    ( spl206_157
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18985,f8752,f21301])).

fof(f21301,plain,
    ( spl206_157
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_157])])).

fof(f18985,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f8754,f4638])).

fof(f22257,plain,
    ( spl206_152
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f18986,f8752,f21232])).

fof(f21232,plain,
    ( spl206_152
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_152])])).

fof(f18986,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f8754,f4638])).

fof(f22196,plain,
    ( spl206_174
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22191,f8752,f22193])).

fof(f22191,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22190,f4635])).

fof(f22190,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK89))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19123,f3634])).

fof(f19123,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4638])).

fof(f22189,plain,
    ( spl206_162
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22188,f8752,f21370])).

fof(f22188,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22187,f4635])).

fof(f22187,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19131,f3634])).

fof(f19131,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4638])).

fof(f22185,plain,
    ( spl206_172
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19139,f8752,f22170])).

fof(f22170,plain,
    ( spl206_172
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_172])])).

fof(f19139,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4638])).

fof(f22184,plain,
    ( spl206_170
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19140,f8752,f22151])).

fof(f22151,plain,
    ( spl206_170
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_170])])).

fof(f19140,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4638])).

fof(f22183,plain,
    ( spl206_173
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22178,f8752,f22180])).

fof(f22178,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22177,f4635])).

fof(f22177,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK128))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19145,f3634])).

fof(f19145,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4638])).

fof(f22176,plain,
    ( spl206_157
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22175,f8752,f21301])).

fof(f22175,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22174,f4635])).

fof(f22174,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19153,f3634])).

fof(f19153,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4638])).

fof(f22173,plain,
    ( spl206_172
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22168,f8752,f22170])).

fof(f22168,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22167,f4635])).

fof(f22167,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK128))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19160,f3634])).

fof(f19160,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4638])).

fof(f22165,plain,
    ( spl206_169
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19162,f8752,f22144])).

fof(f22144,plain,
    ( spl206_169
  <=> k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_169])])).

fof(f19162,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4638])).

fof(f22164,plain,
    ( spl206_171
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22159,f8752,f22161])).

fof(f22159,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22158,f4635])).

fof(f22158,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK162))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19167,f3634])).

fof(f19167,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK162),k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4638])).

fof(f22157,plain,
    ( spl206_152
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22156,f8752,f21232])).

fof(f22156,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22155,f4635])).

fof(f22155,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19175,f3634])).

fof(f19175,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4638])).

fof(f22154,plain,
    ( spl206_170
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22149,f8752,f22151])).

fof(f22149,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22148,f4635])).

fof(f22148,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK162))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19182,f3634])).

fof(f19182,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4638])).

fof(f22147,plain,
    ( spl206_169
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22142,f8752,f22144])).

fof(f22142,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22141,f4635])).

fof(f22141,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK162))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19183,f3634])).

fof(f19183,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4638])).

fof(f22099,plain,
    ( spl206_168
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22098,f8752,f22010])).

fof(f22010,plain,
    ( spl206_168
  <=> k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_168])])).

fof(f22098,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22097,f4635])).

fof(f22097,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19277,f3634])).

fof(f19277,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f4638])).

fof(f22082,plain,
    ( spl206_167
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22081,f8752,f22005])).

fof(f22081,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22080,f4635])).

fof(f22080,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19285,f3634])).

fof(f19285,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4638])).

fof(f22067,plain,
    ( spl206_166
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22066,f8752,f22000])).

fof(f22000,plain,
    ( spl206_166
  <=> k5_relat_1(sK89,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_166])])).

fof(f22066,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22065,f4635])).

fof(f22065,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19292,f3634])).

fof(f19292,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4638])).

fof(f22064,plain,
    ( spl206_165
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22063,f8752,f21995])).

fof(f21995,plain,
    ( spl206_165
  <=> k5_relat_1(sK128,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_165])])).

fof(f22063,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22062,f4635])).

fof(f22062,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19293,f3634])).

fof(f19293,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4638])).

fof(f22061,plain,
    ( spl206_164
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f22060,f8752,f21990])).

fof(f21990,plain,
    ( spl206_164
  <=> k5_relat_1(sK162,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_164])])).

fof(f22060,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f22059,f4635])).

fof(f22059,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f19294,f3634])).

fof(f19294,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4638])).

fof(f22028,plain,
    ( spl206_163
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19607,f8752,f21391])).

fof(f21391,plain,
    ( spl206_163
  <=> k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_163])])).

fof(f19607,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4638])).

fof(f22027,plain,
    ( spl206_162
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19615,f8752,f21370])).

fof(f19615,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4638])).

fof(f22026,plain,
    ( spl206_161
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19622,f8752,f21351])).

fof(f21351,plain,
    ( spl206_161
  <=> k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_161])])).

fof(f19622,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4638])).

fof(f22025,plain,
    ( spl206_160
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19623,f8752,f21344])).

fof(f21344,plain,
    ( spl206_160
  <=> k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_160])])).

fof(f19623,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4638])).

fof(f22024,plain,
    ( spl206_159
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19624,f8752,f21337])).

fof(f21337,plain,
    ( spl206_159
  <=> k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_159])])).

fof(f19624,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4638])).

fof(f22023,plain,
    ( spl206_158
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19629,f8752,f21322])).

fof(f21322,plain,
    ( spl206_158
  <=> k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_158])])).

fof(f19629,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4638])).

fof(f22022,plain,
    ( spl206_157
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19637,f8752,f21301])).

fof(f19637,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4638])).

fof(f22021,plain,
    ( spl206_156
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19644,f8752,f21282])).

fof(f21282,plain,
    ( spl206_156
  <=> k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_156])])).

fof(f19644,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4638])).

fof(f22020,plain,
    ( spl206_155
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19645,f8752,f21275])).

fof(f21275,plain,
    ( spl206_155
  <=> k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_155])])).

fof(f19645,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4638])).

fof(f22019,plain,
    ( spl206_154
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19646,f8752,f21268])).

fof(f21268,plain,
    ( spl206_154
  <=> k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_154])])).

fof(f19646,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4638])).

fof(f22018,plain,
    ( spl206_153
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19651,f8752,f21253])).

fof(f21253,plain,
    ( spl206_153
  <=> k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_153])])).

fof(f19651,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4638])).

fof(f22017,plain,
    ( spl206_152
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19659,f8752,f21232])).

fof(f19659,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4638])).

fof(f22016,plain,
    ( spl206_151
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19666,f8752,f21213])).

fof(f21213,plain,
    ( spl206_151
  <=> k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_151])])).

fof(f19666,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4638])).

fof(f22015,plain,
    ( spl206_150
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19667,f8752,f21206])).

fof(f21206,plain,
    ( spl206_150
  <=> k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_150])])).

fof(f19667,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4638])).

fof(f22014,plain,
    ( spl206_149
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19668,f8752,f21199])).

fof(f21199,plain,
    ( spl206_149
  <=> k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_149])])).

fof(f19668,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4638])).

fof(f22013,plain,
    ( spl206_168
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19761,f8752,f22010])).

fof(f19761,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,k1_xboole_0),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f4298,f8754,f4638])).

fof(f22008,plain,
    ( spl206_167
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19769,f8752,f22005])).

fof(f19769,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,k1_xboole_0),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4298,f8754,f4638])).

fof(f22003,plain,
    ( spl206_166
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19776,f8752,f22000])).

fof(f19776,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,k1_xboole_0),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f4298,f8754,f4638])).

fof(f21998,plain,
    ( spl206_165
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19777,f8752,f21995])).

fof(f19777,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,k1_xboole_0),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f4298,f8754,f4638])).

fof(f21993,plain,
    ( spl206_164
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f19778,f8752,f21990])).

fof(f19778,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,k1_xboole_0),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f4298,f8754,f4638])).

fof(f21394,plain,
    ( spl206_163
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21389,f8752,f21391])).

fof(f21389,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21388,f4635])).

fof(f21388,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK89))) = k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20091,f3634])).

fof(f20091,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK89),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3462,f8754,f4638])).

fof(f21373,plain,
    ( spl206_162
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21368,f8752,f21370])).

fof(f21368,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21367,f4635])).

fof(f21367,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK89))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20099,f3634])).

fof(f20099,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK89),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3462,f8754,f4638])).

fof(f21354,plain,
    ( spl206_161
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21349,f8752,f21351])).

fof(f21349,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21348,f4635])).

fof(f21348,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK89))) = k5_relat_1(sK89,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20106,f3634])).

fof(f20106,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK89),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f8754,f4638])).

fof(f21347,plain,
    ( spl206_160
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21342,f8752,f21344])).

fof(f21342,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21341,f4635])).

fof(f21341,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK89))) = k5_relat_1(sK128,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20107,f3634])).

fof(f20107,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK89),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3462,f8754,f4638])).

fof(f21340,plain,
    ( spl206_159
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21335,f8752,f21337])).

fof(f21335,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21334,f4635])).

fof(f21334,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK89))) = k5_relat_1(sK162,k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20108,f3634])).

fof(f20108,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK89),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3462,f8754,f4638])).

fof(f21325,plain,
    ( spl206_158
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21320,f8752,f21322])).

fof(f21320,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21319,f4635])).

fof(f21319,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK128))) = k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20113,f3634])).

fof(f20113,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK128),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3572,f8754,f4638])).

fof(f21304,plain,
    ( spl206_157
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21299,f8752,f21301])).

fof(f21299,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21298,f4635])).

fof(f21298,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK128))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20121,f3634])).

fof(f20121,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK128),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3572,f8754,f4638])).

fof(f21285,plain,
    ( spl206_156
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21280,f8752,f21282])).

fof(f21280,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21279,f4635])).

fof(f21279,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK128))) = k5_relat_1(sK89,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20128,f3634])).

fof(f20128,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK128),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3572,f8754,f4638])).

fof(f21278,plain,
    ( spl206_155
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21273,f8752,f21275])).

fof(f21273,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21272,f4635])).

fof(f21272,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK128))) = k5_relat_1(sK128,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20129,f3634])).

fof(f20129,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK128),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f8754,f4638])).

fof(f21271,plain,
    ( spl206_154
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21266,f8752,f21268])).

fof(f21266,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21265,f4635])).

fof(f21265,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK128))) = k5_relat_1(sK162,k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20130,f3634])).

fof(f20130,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK128),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3572,f8754,f4638])).

fof(f21256,plain,
    ( spl206_153
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21251,f8752,f21253])).

fof(f21251,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21250,f4635])).

fof(f21250,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK3),k5_relat_1(k1_xboole_0,sK162))) = k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20135,f3634])).

fof(f20135,plain,
    ( k5_relat_1(k1_xboole_0,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(k1_xboole_0,sK162),k5_relat_1(k1_xboole_0,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f3900,f8754,f4638])).

fof(f21235,plain,
    ( spl206_152
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21230,f8752,f21232])).

fof(f21230,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21229,f4635])).

fof(f21229,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK3,sK3),k5_relat_1(sK3,sK162))) = k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20143,f3634])).

fof(f20143,plain,
    ( k5_relat_1(sK3,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK3,sK162),k5_relat_1(sK3,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f3900,f8754,f4638])).

fof(f21216,plain,
    ( spl206_151
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21211,f8752,f21213])).

fof(f21211,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21210,f4635])).

fof(f21210,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK89,sK3),k5_relat_1(sK89,sK162))) = k5_relat_1(sK89,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20150,f3634])).

fof(f20150,plain,
    ( k5_relat_1(sK89,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK89,sK162),k5_relat_1(sK89,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f3900,f8754,f4638])).

fof(f21209,plain,
    ( spl206_150
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21204,f8752,f21206])).

fof(f21204,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21203,f4635])).

fof(f21203,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK128,sK3),k5_relat_1(sK128,sK162))) = k5_relat_1(sK128,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20151,f3634])).

fof(f20151,plain,
    ( k5_relat_1(sK128,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK128,sK162),k5_relat_1(sK128,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f3900,f8754,f4638])).

fof(f21202,plain,
    ( spl206_149
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21197,f8752,f21199])).

fof(f21197,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21196,f4635])).

fof(f21196,plain,
    ( k3_tarski(k2_tarski(k5_relat_1(sK162,sK3),k5_relat_1(sK162,sK162))) = k5_relat_1(sK162,k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20152,f3634])).

fof(f20152,plain,
    ( k5_relat_1(sK162,k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k5_relat_1(sK162,sK162),k5_relat_1(sK162,sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f8754,f4638])).

fof(f21011,plain,
    ( spl206_148
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f21010,f8752,f20985])).

fof(f20985,plain,
    ( spl206_148
  <=> k1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_148])])).

fof(f21010,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21009,f4635])).

fof(f21009,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f21008,f3391])).

fof(f21008,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20245,f3634])).

fof(f20245,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4639])).

fof(f4639,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k1_relat_1(X0),k1_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3297,f3631,f3631])).

fof(f3297,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1621])).

fof(f1621,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f743])).

fof(f743,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k1_relat_1(X0),k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relat_1)).

fof(f20991,plain,
    ( spl206_147
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20260,f8752,f20937])).

fof(f20937,plain,
    ( spl206_147
  <=> k1_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_147])])).

fof(f20260,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4639])).

fof(f20990,plain,
    ( spl206_146
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20261,f8752,f20930])).

fof(f20930,plain,
    ( spl206_146
  <=> k1_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_146])])).

fof(f20261,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4639])).

fof(f20989,plain,
    ( spl206_145
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20262,f8752,f20923])).

fof(f20923,plain,
    ( spl206_145
  <=> k1_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_145])])).

fof(f20262,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4639])).

fof(f20988,plain,
    ( spl206_148
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20983,f8752,f20985])).

fof(f20983,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20267,f3391])).

fof(f20267,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_relat_1(k1_xboole_0),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4639])).

fof(f20940,plain,
    ( spl206_147
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20935,f8752,f20937])).

fof(f20935,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20934,f4635])).

fof(f20934,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK89))) = k1_relat_1(k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20282,f3634])).

fof(f20282,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k1_relat_1(sK89),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4639])).

fof(f20933,plain,
    ( spl206_146
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20928,f8752,f20930])).

fof(f20928,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20927,f4635])).

fof(f20927,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK128))) = k1_relat_1(k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20283,f3634])).

fof(f20283,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k1_relat_1(sK128),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4639])).

fof(f20926,plain,
    ( spl206_145
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20921,f8752,f20923])).

fof(f20921,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20920,f4635])).

fof(f20920,plain,
    ( k3_tarski(k2_tarski(k1_relat_1(sK3),k1_relat_1(sK162))) = k1_relat_1(k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20284,f3634])).

fof(f20284,plain,
    ( k1_relat_1(k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k1_relat_1(sK162),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4639])).

fof(f20911,plain,
    ( spl206_144
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20910,f8752,f20896])).

fof(f20896,plain,
    ( spl206_144
  <=> k2_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_144])])).

fof(f20910,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20909,f4635])).

fof(f20909,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20908,f3392])).

fof(f20908,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20289,f3634])).

fof(f20289,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4640])).

fof(f4640,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k2_relat_1(X0),k2_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3298,f3631,f3631])).

fof(f3298,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1622])).

fof(f1622,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f830])).

fof(f830,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k2_relat_1(X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_relat_1)).

fof(f20902,plain,
    ( spl206_143
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20304,f8752,f20859])).

fof(f20859,plain,
    ( spl206_143
  <=> k2_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_143])])).

fof(f20304,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4640])).

fof(f20901,plain,
    ( spl206_142
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20305,f8752,f20852])).

fof(f20852,plain,
    ( spl206_142
  <=> k2_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_142])])).

fof(f20305,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4640])).

fof(f20900,plain,
    ( spl206_141
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20306,f8752,f20845])).

fof(f20845,plain,
    ( spl206_141
  <=> k2_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_141])])).

fof(f20306,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4640])).

fof(f20899,plain,
    ( spl206_144
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20894,f8752,f20896])).

fof(f20894,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20311,f3392])).

fof(f20311,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k2_relat_1(k1_xboole_0),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4640])).

fof(f20862,plain,
    ( spl206_143
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20857,f8752,f20859])).

fof(f20857,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20856,f4635])).

fof(f20856,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK89))) = k2_relat_1(k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20326,f3634])).

fof(f20326,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k2_relat_1(sK89),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4640])).

fof(f20855,plain,
    ( spl206_142
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20850,f8752,f20852])).

fof(f20850,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20849,f4635])).

fof(f20849,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK128))) = k2_relat_1(k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20327,f3634])).

fof(f20327,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k2_relat_1(sK128),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4640])).

fof(f20848,plain,
    ( spl206_141
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20843,f8752,f20845])).

fof(f20843,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20842,f4635])).

fof(f20842,plain,
    ( k3_tarski(k2_tarski(k2_relat_1(sK3),k2_relat_1(sK162))) = k2_relat_1(k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20328,f3634])).

fof(f20328,plain,
    ( k2_relat_1(k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k2_relat_1(sK162),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4640])).

fof(f20833,plain,
    ( spl206_140
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20828,f8752,f20830])).

fof(f20830,plain,
    ( spl206_140
  <=> k3_relat_1(sK3) = k3_tarski(k2_tarski(k2_relat_1(sK3),k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_140])])).

fof(f20828,plain,
    ( k3_relat_1(sK3) = k3_tarski(k2_tarski(k2_relat_1(sK3),k1_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20333,f3634])).

fof(f20333,plain,
    ( k3_relat_1(sK3) = k3_tarski(k2_tarski(k1_relat_1(sK3),k2_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f8754,f4644])).

fof(f4644,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k2_tarski(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3383,f3631])).

fof(f3383,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1701])).

fof(f1701,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f658])).

fof(f658,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f20827,plain,
    ( spl206_139
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20826,f8752,f20815])).

fof(f20815,plain,
    ( spl206_139
  <=> k3_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k3_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_139])])).

fof(f20826,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20825,f4635])).

fof(f20825,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_xboole_0,k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20824,f3765])).

fof(f20824,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k3_relat_1(k1_xboole_0),k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20334,f3634])).

fof(f20334,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4718])).

fof(f4718,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k3_relat_1(X0),k3_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f3759,f3631,f3631])).

fof(f3759,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1875])).

fof(f1875,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f836])).

fof(f836,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k3_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_relat_1(X0),k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relat_1)).

fof(f20821,plain,
    ( spl206_138
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20349,f8752,f20781])).

fof(f20781,plain,
    ( spl206_138
  <=> k3_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_138])])).

fof(f20349,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4718])).

fof(f20820,plain,
    ( spl206_137
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20350,f8752,f20774])).

fof(f20774,plain,
    ( spl206_137
  <=> k3_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_137])])).

fof(f20350,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4718])).

fof(f20819,plain,
    ( spl206_136
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20351,f8752,f20767])).

fof(f20767,plain,
    ( spl206_136
  <=> k3_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_136])])).

fof(f20351,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4718])).

fof(f20818,plain,
    ( spl206_139
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20813,f8752,f20815])).

fof(f20813,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20356,f3765])).

fof(f20356,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k3_relat_1(k1_xboole_0),k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4718])).

fof(f20784,plain,
    ( spl206_138
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20779,f8752,f20781])).

fof(f20779,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20778,f4635])).

fof(f20778,plain,
    ( k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK89))) = k3_relat_1(k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20371,f3634])).

fof(f20371,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k3_relat_1(sK89),k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4718])).

fof(f20777,plain,
    ( spl206_137
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20772,f8752,f20774])).

fof(f20772,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20771,f4635])).

fof(f20771,plain,
    ( k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK128))) = k3_relat_1(k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20372,f3634])).

fof(f20372,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k3_relat_1(sK128),k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4718])).

fof(f20770,plain,
    ( spl206_136
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20765,f8752,f20767])).

fof(f20765,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20764,f4635])).

fof(f20764,plain,
    ( k3_tarski(k2_tarski(k3_relat_1(sK3),k3_relat_1(sK162))) = k3_relat_1(k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20373,f3634])).

fof(f20373,plain,
    ( k3_relat_1(k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k3_relat_1(sK162),k3_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4718])).

fof(f20755,plain,
    ( spl206_135
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20754,f8752,f20740])).

fof(f20740,plain,
    ( spl206_135
  <=> k4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_135])])).

fof(f20754,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20753,f4635])).

fof(f20753,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k1_xboole_0,k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20752,f4240])).

fof(f20752,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20384,f3634])).

fof(f20384,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,k1_xboole_0))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(k1_xboole_0)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4865])).

fof(f4865,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k3_tarski(k2_tarski(X0,X1))) = k3_tarski(k2_tarski(k4_relat_1(X0),k4_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f4230,f3631,f3631])).

fof(f4230,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2141])).

fof(f2141,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f841])).

fof(f841,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k2_xboole_0(X0,X1)) = k2_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_relat_1)).

fof(f20746,plain,
    ( spl206_134
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20399,f8752,f20703])).

fof(f20703,plain,
    ( spl206_134
  <=> k4_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_134])])).

fof(f20399,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4865])).

fof(f20745,plain,
    ( spl206_133
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20400,f8752,f20696])).

fof(f20696,plain,
    ( spl206_133
  <=> k4_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_133])])).

fof(f20400,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4865])).

fof(f20744,plain,
    ( spl206_132
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20401,f8752,f20689])).

fof(f20689,plain,
    ( spl206_132
  <=> k4_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_132])])).

fof(f20401,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4865])).

fof(f20743,plain,
    ( spl206_135
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20738,f8752,f20740])).

fof(f20738,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k1_xboole_0,k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20406,f4240])).

fof(f20406,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(k1_xboole_0,sK3))) = k3_tarski(k2_tarski(k4_relat_1(k1_xboole_0),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f4298,f8754,f4865])).

fof(f20706,plain,
    ( spl206_134
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20701,f8752,f20703])).

fof(f20701,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK89))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20700,f4635])).

fof(f20700,plain,
    ( k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK89))) = k4_relat_1(k3_tarski(k2_tarski(sK89,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20421,f3634])).

fof(f20421,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK89,sK3))) = k3_tarski(k2_tarski(k4_relat_1(sK89),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4865])).

fof(f20699,plain,
    ( spl206_133
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20694,f8752,f20696])).

fof(f20694,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK128))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20693,f4635])).

fof(f20693,plain,
    ( k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK128))) = k4_relat_1(k3_tarski(k2_tarski(sK128,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20422,f3634])).

fof(f20422,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK128,sK3))) = k3_tarski(k2_tarski(k4_relat_1(sK128),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4865])).

fof(f20692,plain,
    ( spl206_132
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20687,f8752,f20689])).

fof(f20687,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK3,sK162))) = k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20686,f4635])).

fof(f20686,plain,
    ( k3_tarski(k2_tarski(k4_relat_1(sK3),k4_relat_1(sK162))) = k4_relat_1(k3_tarski(k2_tarski(sK162,sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20423,f3634])).

fof(f20423,plain,
    ( k4_relat_1(k3_tarski(k2_tarski(sK162,sK3))) = k3_tarski(k2_tarski(k4_relat_1(sK162),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4865])).

fof(f20667,plain,
    ( spl206_131
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20443,f8752,f20664])).

fof(f20664,plain,
    ( spl206_131
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK89))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_131])])).

fof(f20443,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK89)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4866])).

fof(f4866,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k4_relat_1(X0),k4_xboole_0(k4_relat_1(X0),k4_relat_1(X1)))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f4231,f3248,f3248])).

fof(f4231,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2142])).

fof(f2142,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f840])).

fof(f840,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k3_xboole_0(X0,X1)) = k3_xboole_0(k4_relat_1(X0),k4_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relat_1)).

fof(f20662,plain,
    ( spl206_130
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20444,f8752,f20659])).

fof(f20659,plain,
    ( spl206_130
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK128))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_130])])).

fof(f20444,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK128)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4866])).

fof(f20657,plain,
    ( spl206_129
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20445,f8752,f20654])).

fof(f20654,plain,
    ( spl206_129
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK162))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_129])])).

fof(f20445,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))) = k4_xboole_0(k4_relat_1(sK3),k4_xboole_0(k4_relat_1(sK3),k4_relat_1(sK162)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4866])).

fof(f20626,plain,
    ( spl206_128
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20621,f8752,f20623])).

fof(f20623,plain,
    ( spl206_128
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))) = k4_xboole_0(k4_relat_1(sK89),k4_xboole_0(k4_relat_1(sK89),k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_128])])).

fof(f20621,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK89))) = k4_xboole_0(k4_relat_1(sK89),k4_xboole_0(k4_relat_1(sK89),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20465,f4596])).

fof(f20465,plain,
    ( k4_relat_1(k4_xboole_0(sK89,k4_xboole_0(sK89,sK3))) = k4_xboole_0(k4_relat_1(sK89),k4_xboole_0(k4_relat_1(sK89),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3462,f8754,f4866])).

fof(f20620,plain,
    ( spl206_127
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20615,f8752,f20617])).

fof(f20617,plain,
    ( spl206_127
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))) = k4_xboole_0(k4_relat_1(sK128),k4_xboole_0(k4_relat_1(sK128),k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_127])])).

fof(f20615,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK128))) = k4_xboole_0(k4_relat_1(sK128),k4_xboole_0(k4_relat_1(sK128),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20466,f4596])).

fof(f20466,plain,
    ( k4_relat_1(k4_xboole_0(sK128,k4_xboole_0(sK128,sK3))) = k4_xboole_0(k4_relat_1(sK128),k4_xboole_0(k4_relat_1(sK128),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3572,f8754,f4866])).

fof(f20614,plain,
    ( spl206_126
    | ~ spl206_105 ),
    inference(avatar_split_clause,[],[f20609,f8752,f20611])).

fof(f20611,plain,
    ( spl206_126
  <=> k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))) = k4_xboole_0(k4_relat_1(sK162),k4_xboole_0(k4_relat_1(sK162),k4_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_126])])).

fof(f20609,plain,
    ( k4_relat_1(k4_xboole_0(sK3,k4_xboole_0(sK3,sK162))) = k4_xboole_0(k4_relat_1(sK162),k4_xboole_0(k4_relat_1(sK162),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(forward_demodulation,[],[f20467,f4596])).

fof(f20467,plain,
    ( k4_relat_1(k4_xboole_0(sK162,k4_xboole_0(sK162,sK3))) = k4_xboole_0(k4_relat_1(sK162),k4_xboole_0(k4_relat_1(sK162),k4_relat_1(sK3)))
    | ~ spl206_105 ),
    inference(unit_resulting_resolution,[],[f3900,f8754,f4866])).

fof(f8860,plain,
    ( spl206_125
    | spl206_124
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8643,f5112,f8853,f8858])).

fof(f8858,plain,
    ( spl206_125
  <=> ! [X11,X10] :
        ( r1_tarski(sK0,X10)
        | ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(X11,X10)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_125])])).

fof(f8853,plain,
    ( spl206_124
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_124])])).

fof(f8643,plain,
    ( ! [X10,X11] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(sK0,X10)
        | ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(X11,X10)) )
    | ~ spl206_3 ),
    inference(superposition,[],[f5114,f2917])).

fof(f2917,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X1,X3)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1376])).

fof(f1376,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f1375])).

fof(f1375,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X1,X3)
        & r1_tarski(X0,X2) )
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f354])).

fof(f354,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f8856,plain,
    ( spl206_123
    | spl206_124
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8642,f5112,f8853,f8850])).

fof(f8850,plain,
    ( spl206_123
  <=> ! [X9,X8] :
        ( r1_tarski(sK1,X8)
        | ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(X8,X9)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_123])])).

fof(f8642,plain,
    ( ! [X8,X9] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
        | r1_tarski(sK1,X8)
        | ~ r1_tarski(k2_zfmisc_1(sK1,sK0),k2_zfmisc_1(X8,X9)) )
    | ~ spl206_3 ),
    inference(superposition,[],[f5114,f2916])).

fof(f2916,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X0,X2)
      | k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1376])).

fof(f8848,plain,
    ( spl206_122
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8554,f5112,f8844])).

fof(f8844,plain,
    ( spl206_122
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_zfmisc_1(k3_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_122])])).

fof(f8554,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_zfmisc_1(k3_tarski(sK0)))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f4882,f5114,f2831])).

fof(f2831,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f1318])).

fof(f1318,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1317])).

fof(f1317,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_relset_1)).

fof(f8847,plain,
    ( spl206_122
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8558,f5112,f8844])).

fof(f8558,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_zfmisc_1(k3_tarski(sK0)))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f4881,f5114,f2831])).

fof(f8842,plain,
    ( spl206_121
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8560,f5112,f8838])).

fof(f8838,plain,
    ( spl206_121
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_121])])).

fof(f8560,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f4083,f5114,f2831])).

fof(f8841,plain,
    ( spl206_121
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8561,f5112,f8838])).

fof(f8561,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4881,f4083,f5114,f2831])).

fof(f8836,plain,
    ( spl206_120
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8562,f5112,f8833])).

fof(f8833,plain,
    ( spl206_120
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),k1_zfmisc_1(k3_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_120])])).

fof(f8562,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),k1_zfmisc_1(k3_tarski(sK0)))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f4083,f5114,f2831])).

fof(f8831,plain,
    ( spl206_119
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8568,f5112,f5107,f8827])).

fof(f8827,plain,
    ( spl206_119
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_119])])).

fof(f8568,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f5114,f2831])).

fof(f8830,plain,
    ( spl206_119
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8569,f5112,f5107,f8827])).

fof(f8569,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f5114,f2831])).

fof(f8825,plain,
    ( spl206_118
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8570,f5112,f5107,f8822])).

fof(f8822,plain,
    ( spl206_118
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_zfmisc_1(k3_tarski(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_118])])).

fof(f8570,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,k1_zfmisc_1(k3_tarski(sK0)))))
    | ~ spl206_2
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f5109,f5114,f2831])).

fof(f8820,plain,
    ( spl206_117
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8572,f5112,f8816])).

fof(f8816,plain,
    ( spl206_117
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_117])])).

fof(f8572,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f2839])).

fof(f2839,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f1325])).

fof(f1325,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f1324])).

fof(f1324,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f1231])).

fof(f1231,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

fof(f8819,plain,
    ( spl206_117
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8573,f5112,f8816])).

fof(f8573,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4881,f5114,f2839])).

fof(f8814,plain,
    ( spl206_116
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8574,f5112,f8811])).

fof(f8811,plain,
    ( spl206_116
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_116])])).

fof(f8574,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(k1_relat_1(sK3))),sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f5114,f2839])).

fof(f8809,plain,
    ( spl206_115
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8576,f5112,f8805])).

fof(f8805,plain,
    ( spl206_115
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_115])])).

fof(f8576,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK3))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f2840])).

fof(f2840,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f1327])).

fof(f1327,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f1326])).

fof(f1326,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f1232])).

fof(f1232,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

fof(f8808,plain,
    ( spl206_115
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8577,f5112,f8805])).

fof(f8577,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK3))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4881,f5114,f2840])).

fof(f8803,plain,
    ( spl206_114
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8578,f5112,f8800])).

fof(f8800,plain,
    ( spl206_114
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_zfmisc_1(k3_tarski(k2_relat_1(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_114])])).

fof(f8578,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_zfmisc_1(k3_tarski(k2_relat_1(sK3))))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4083,f5114,f2840])).

fof(f8798,plain,
    ( spl206_113
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8585,f5112,f8795])).

fof(f8795,plain,
    ( spl206_113
  <=> m1_subset_1(k2_relat_1(sK6(sK3,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_113])])).

fof(f8585,plain,
    ( m1_subset_1(k2_relat_1(sK6(sK3,k1_xboole_0)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4871,f5114,f2841])).

fof(f2841,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f1329])).

fof(f1329,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f1328])).

fof(f1328,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f1247])).

fof(f1247,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_relset_1)).

fof(f8793,plain,
    ( spl206_105
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8588,f5112,f8752])).

fof(f8588,plain,
    ( v1_relat_1(sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f2844])).

fof(f2844,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1333])).

fof(f1333,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f8792,plain,
    ( spl206_112
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8589,f5112,f8789])).

fof(f8589,plain,
    ( v4_relat_1(sK3,sK1)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4261])).

fof(f4261,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2170])).

fof(f2170,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f8787,plain,
    ( spl206_111
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8590,f5112,f8784])).

fof(f8590,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4262])).

fof(f4262,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2170])).

fof(f8782,plain,
    ( spl206_110
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8777,f5112,f8779])).

fof(f8779,plain,
    ( spl206_110
  <=> r1_tarski(k3_relat_1(sK3),k3_tarski(k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_110])])).

fof(f8777,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k2_tarski(sK0,sK1)))
    | ~ spl206_3 ),
    inference(forward_demodulation,[],[f8591,f4635])).

fof(f8591,plain,
    ( r1_tarski(k3_relat_1(sK3),k3_tarski(k2_tarski(sK1,sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4400])).

fof(f4400,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_relat_1(X2),k3_tarski(k2_tarski(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_unfolding,[],[f2938,f3631])).

fof(f2938,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1383])).

fof(f1383,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => r1_tarski(k3_relat_1(X2),k2_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relset_1)).

fof(f8776,plain,
    ( spl206_109
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8592,f5112,f8772])).

fof(f8772,plain,
    ( spl206_109
  <=> r2_relset_1(sK1,sK0,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_109])])).

fof(f8592,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f5091])).

fof(f5091,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f4870])).

fof(f4870,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f2751])).

fof(f2751,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f2203])).

fof(f2203,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f1266])).

fof(f1266,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1265])).

fof(f1265,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1226])).

fof(f1226,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f8775,plain,
    ( spl206_109
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8593,f5112,f8772])).

fof(f8593,plain,
    ( r2_relset_1(sK1,sK0,sK3,sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f5092])).

fof(f5092,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_relset_1(X1,X2,X0,X0) ) ),
    inference(condensation,[],[f2753])).

fof(f2753,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1270])).

fof(f1270,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1269])).

fof(f1269,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_relset_1(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => r2_relset_1(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

fof(f8770,plain,
    ( spl206_108
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8594,f5112,f8767])).

fof(f8767,plain,
    ( spl206_108
  <=> r1_tarski(sK3,k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_108])])).

fof(f8594,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f2797])).

fof(f2797,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2216])).

fof(f2216,plain,(
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

fof(f8765,plain,
    ( ~ spl206_107
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8595,f5112,f8762])).

fof(f8595,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2972,f5114,f2852])).

fof(f2972,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f369])).

fof(f369,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f8760,plain,
    ( ~ spl206_106
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8596,f5112,f8757])).

fof(f8757,plain,
    ( spl206_106
  <=> r2_hidden(sK177(k2_zfmisc_1(sK1,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_106])])).

fof(f8596,plain,
    ( ~ r2_hidden(sK177(k2_zfmisc_1(sK1,sK0)),sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4021,f5114,f2852])).

fof(f8755,plain,
    ( spl206_105
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8597,f5112,f8752])).

fof(f8597,plain,
    ( v1_relat_1(sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2973,f5114,f2873])).

fof(f2973,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f8750,plain,
    ( spl206_103
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8602,f5112,f8740])).

fof(f8740,plain,
    ( spl206_103
  <=> r1_xboole_0(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_103])])).

fof(f8602,plain,
    ( r1_xboole_0(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f5114,f3678])).

fof(f3678,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2558])).

fof(f2558,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f1844])).

fof(f1844,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f517])).

fof(f517,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

fof(f8749,plain,
    ( spl206_104
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8603,f5112,f8745])).

fof(f8745,plain,
    ( spl206_104
  <=> r1_xboole_0(k1_xboole_0,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_104])])).

fof(f8603,plain,
    ( r1_xboole_0(k1_xboole_0,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2830,f2868,f5114,f3678])).

fof(f8748,plain,
    ( spl206_104
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8604,f5112,f8745])).

fof(f8604,plain,
    ( r1_xboole_0(k1_xboole_0,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2830,f2878,f5114,f3678])).

fof(f8743,plain,
    ( spl206_103
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8605,f5112,f8740])).

fof(f8605,plain,
    ( r1_xboole_0(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f4882,f5114,f5114,f3678])).

fof(f8738,plain,
    ( spl206_99
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8606,f5112,f8717])).

fof(f8606,plain,
    ( r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f3491,f2868,f5114,f3679])).

fof(f3679,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ r1_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2559])).

fof(f2559,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,X2)
              | ~ r1_tarski(X1,k3_subset_1(X0,X2)) )
            & ( r1_tarski(X1,k3_subset_1(X0,X2))
              | ~ r1_xboole_0(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f1845])).

fof(f1845,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f516])).

fof(f516,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

fof(f8737,plain,
    ( spl206_99
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8607,f5112,f8717])).

fof(f8607,plain,
    ( r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f3491,f2878,f5114,f3679])).

fof(f8736,plain,
    ( spl206_102
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8608,f5112,f8733])).

fof(f8608,plain,
    ( r1_xboole_0(k1_xboole_0,sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2868,f2830,f5114,f3680])).

fof(f3680,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X1,X2)
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2559])).

fof(f8731,plain,
    ( spl206_101
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8609,f5112,f8728])).

fof(f8728,plain,
    ( spl206_101
  <=> sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(sK1,sK0)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_101])])).

fof(f8609,plain,
    ( sK3 = k9_relat_1(k6_relat_1(k2_zfmisc_1(sK1,sK0)),sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f3811])).

fof(f3811,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f1921])).

fof(f1921,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f983])).

fof(f983,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f8726,plain,
    ( spl206_100
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8612,f5112,f8722])).

fof(f8722,plain,
    ( spl206_100
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_100])])).

fof(f8612,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2830,f2868,f5114,f4095])).

fof(f4095,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2692])).

fof(f2692,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f2101])).

fof(f2101,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f505])).

fof(f505,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f8725,plain,
    ( spl206_100
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8613,f5112,f8722])).

fof(f8613,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2830,f2878,f5114,f4095])).

fof(f8720,plain,
    ( spl206_99
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8619,f5112,f8717])).

fof(f8619,plain,
    ( r1_tarski(sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2868,f2830,f5114,f4108])).

fof(f4108,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2113])).

fof(f2113,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2112])).

fof(f2112,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X2,k3_subset_1(X0,X1))
          | ~ r1_tarski(X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f509])).

fof(f509,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,k3_subset_1(X0,X2))
           => r1_tarski(X2,k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

fof(f8715,plain,
    ( spl206_98
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8620,f5112,f8711])).

fof(f8711,plain,
    ( spl206_98
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,k1_xboole_0)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_98])])).

fof(f8620,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,k1_xboole_0)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2868,f5114,f4109])).

fof(f4109,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2114])).

fof(f2114,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f514])).

fof(f514,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_subset_1)).

fof(f8714,plain,
    ( spl206_98
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8621,f5112,f8711])).

fof(f8621,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,k1_xboole_0)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2878,f5114,f4109])).

fof(f8708,plain,
    ( spl206_94
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8623,f5112,f8687])).

fof(f8687,plain,
    ( spl206_94
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_94])])).

fof(f8623,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f5114,f4109])).

fof(f8707,plain,
    ( spl206_97
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8624,f5112,f8704])).

fof(f8704,plain,
    ( spl206_97
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK19(k2_zfmisc_1(sK1,sK0)))),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_97])])).

fof(f8624,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK19(k2_zfmisc_1(sK1,sK0)))),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2869,f5114,f4109])).

fof(f8702,plain,
    ( spl206_96
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8625,f5112,f8699])).

fof(f8699,plain,
    ( spl206_96
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_96])])).

fof(f8625,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2871,f5114,f4109])).

fof(f8697,plain,
    ( spl206_95
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8626,f5112,f8693])).

fof(f8693,plain,
    ( spl206_95
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_95])])).

fof(f8626,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2868,f5114,f4109])).

fof(f8696,plain,
    ( spl206_95
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8627,f5112,f8693])).

fof(f8627,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),k1_xboole_0))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2878,f5114,f4109])).

fof(f8690,plain,
    ( spl206_94
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8629,f5112,f8687])).

fof(f8629,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f5114,f4109])).

fof(f8685,plain,
    ( spl206_93
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8630,f5112,f8682])).

fof(f8682,plain,
    ( spl206_93
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK19(k2_zfmisc_1(sK1,sK0)),sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK19(k2_zfmisc_1(sK1,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_93])])).

fof(f8630,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK19(k2_zfmisc_1(sK1,sK0)),sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK19(k2_zfmisc_1(sK1,sK0))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2869,f5114,f4109])).

fof(f8680,plain,
    ( spl206_92
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8631,f5112,f8677])).

fof(f8677,plain,
    ( spl206_92
  <=> r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_92])])).

fof(f8631,plain,
    ( r1_tarski(k3_subset_1(k2_zfmisc_1(sK1,sK0),k4_subset_1(k2_zfmisc_1(sK1,sK0),sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))),sK3)),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2871,f5114,f4109])).

fof(f8675,plain,
    ( spl206_91
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8632,f5112,f8672])).

fof(f8672,plain,
    ( spl206_91
  <=> k2_subset_1(k2_zfmisc_1(sK1,sK0)) = k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_91])])).

fof(f8632,plain,
    ( k2_subset_1(k2_zfmisc_1(sK1,sK0)) = k4_subset_1(k2_zfmisc_1(sK1,sK0),sK3,k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4112])).

fof(f4112,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2116])).

fof(f2116,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f503])).

fof(f503,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f8670,plain,
    ( spl206_90
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8633,f5112,f8667])).

fof(f8667,plain,
    ( spl206_90
  <=> sK3 = k3_subset_1(k2_zfmisc_1(sK1,sK0),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_90])])).

fof(f8633,plain,
    ( sK3 = k3_subset_1(k2_zfmisc_1(sK1,sK0),k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4113])).

fof(f4113,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2117])).

fof(f2117,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f8665,plain,
    ( spl206_89
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8634,f5112,f8662])).

fof(f8662,plain,
    ( spl206_89
  <=> k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK1,sK0),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_89])])).

fof(f8634,plain,
    ( k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3) = k4_xboole_0(k2_zfmisc_1(sK1,sK0),sK3)
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4114])).

fof(f4114,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2118])).

fof(f2118,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f8660,plain,
    ( spl206_88
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8635,f5112,f8657])).

fof(f8657,plain,
    ( spl206_88
  <=> m1_subset_1(k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_88])])).

fof(f8635,plain,
    ( m1_subset_1(k3_subset_1(k2_zfmisc_1(sK1,sK0),sK3),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f5114,f4115])).

fof(f4115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2119])).

fof(f2119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f8655,plain,
    ( spl206_87
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8636,f5112,f8651])).

fof(f8651,plain,
    ( spl206_87
  <=> r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_87])])).

fof(f8636,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2883,f5114,f2861])).

fof(f2861,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f1352])).

fof(f1352,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f1351])).

fof(f1351,plain,(
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

fof(f2883,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f477])).

fof(f477,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f8654,plain,
    ( spl206_87
    | ~ spl206_3 ),
    inference(avatar_split_clause,[],[f8637,f5112,f8651])).

fof(f8637,plain,
    ( r2_hidden(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl206_3 ),
    inference(unit_resulting_resolution,[],[f2883,f5114,f2864])).

fof(f2864,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f2248])).

fof(f2248,plain,(
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
    inference(nnf_transformation,[],[f1355])).

fof(f1355,plain,(
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

fof(f8541,plain,
    ( spl206_86
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8070,f7635,f8538])).

fof(f8538,plain,
    ( spl206_86
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK89,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_86])])).

fof(f8070,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK89,k1_xboole_0),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3462,f7637,f2997])).

fof(f8536,plain,
    ( spl206_85
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8071,f7635,f8533])).

fof(f8533,plain,
    ( spl206_85
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK128,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_85])])).

fof(f8071,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK128,k1_xboole_0),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3572,f7637,f2997])).

fof(f8531,plain,
    ( spl206_84
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8072,f7635,f8528])).

fof(f8528,plain,
    ( spl206_84
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK162,k1_xboole_0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_84])])).

fof(f8072,plain,
    ( k1_xboole_0 = k7_relat_1(k7_relat_1(sK162,k1_xboole_0),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3900,f7637,f2997])).

fof(f8524,plain,
    ( spl206_81
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8097,f7635,f8461])).

fof(f8461,plain,
    ( spl206_81
  <=> r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_81])])).

fof(f8097,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4871,f4882,f7637,f3659])).

fof(f8517,plain,
    ( spl206_81
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8105,f7635,f8461])).

fof(f8105,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4871,f4881,f7637,f3659])).

fof(f8500,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8132,f7635,f8482])).

fof(f8482,plain,
    ( spl206_82
  <=> r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_82])])).

fof(f8132,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4882,f4871,f7637,f3659])).

fof(f8499,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8133,f7635,f8482])).

fof(f8133,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4881,f4871,f7637,f3659])).

fof(f8498,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8134,f7635,f8482])).

fof(f8134,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f2830,f4871,f7637,f3659])).

fof(f8497,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8496,f7635,f8482])).

fof(f8496,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8135,f3489])).

fof(f8135,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4365,f4871,f7637,f3659])).

fof(f8495,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8494,f7635,f8482])).

fof(f8494,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8136,f3489])).

fof(f8136,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(k1_xboole_0,X0),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3657,f4871,f7637,f3659])).

fof(f8493,plain,
    ( spl206_83
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8137,f7635,f8490])).

fof(f8490,plain,
    ( spl206_83
  <=> r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK6(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_83])])).

fof(f8137,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4871,f4871,f7637,f3659])).

fof(f8488,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8487,f7635,f8482])).

fof(f8487,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8486,f3391])).

fof(f8486,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8138,f4893])).

fof(f8138,plain,
    ( ! [X0] : r1_xboole_0(k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f2970,f4871,f7637,f3659])).

fof(f8485,plain,
    ( spl206_82
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8480,f7635,f8482])).

fof(f8480,plain,
    ( r1_xboole_0(k1_xboole_0,k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8479,f3392])).

fof(f8479,plain,
    ( r1_xboole_0(k2_relat_1(k1_xboole_0),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8139,f4892])).

fof(f8139,plain,
    ( ! [X0] : r1_xboole_0(k2_relat_1(k2_zfmisc_1(X0,k1_xboole_0)),k2_relat_1(sK6(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f2971,f4871,f7637,f3659])).

fof(f8464,plain,
    ( spl206_81
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8161,f7635,f8461])).

fof(f8161,plain,
    ( r1_xboole_0(k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4871,f7637,f3665])).

fof(f8455,plain,
    ( spl206_80
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8172,f7635,f8452])).

fof(f8452,plain,
    ( spl206_80
  <=> r1_xboole_0(k9_relat_1(sK162,k1_xboole_0),k9_relat_1(sK162,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_80])])).

fof(f8172,plain,
    ( r1_xboole_0(k9_relat_1(sK162,k1_xboole_0),k9_relat_1(sK162,sK1))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f3902,f7637,f3666])).

fof(f8449,plain,
    ( spl206_79
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8187,f7635,f8446])).

fof(f8446,plain,
    ( spl206_79
  <=> r1_xboole_0(k10_relat_1(sK89,k1_xboole_0),k10_relat_1(sK89,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_79])])).

fof(f8187,plain,
    ( r1_xboole_0(k10_relat_1(sK89,k1_xboole_0),k10_relat_1(sK89,sK1))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f7637,f3688])).

fof(f8444,plain,
    ( spl206_78
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8188,f7635,f8441])).

fof(f8441,plain,
    ( spl206_78
  <=> r1_xboole_0(k10_relat_1(sK162,k1_xboole_0),k10_relat_1(sK162,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_78])])).

fof(f8188,plain,
    ( r1_xboole_0(k10_relat_1(sK162,k1_xboole_0),k10_relat_1(sK162,sK1))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f7637,f3688])).

fof(f8430,plain,
    ( spl206_77
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8205,f7635,f8427])).

fof(f8427,plain,
    ( spl206_77
  <=> sK1 = k3_tarski(k2_tarski(k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_77])])).

fof(f8205,plain,
    ( sK1 = k3_tarski(k2_tarski(k1_xboole_0,sK1))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3491,f4641,f7637,f4602])).

fof(f8341,plain,
    ( spl206_76
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8340,f7635,f8331])).

fof(f8331,plain,
    ( spl206_76
  <=> r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_76])])).

fof(f8340,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK1)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8236,f4635])).

fof(f8236,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4948,f7637,f4620])).

fof(f8338,plain,
    ( spl206_76
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8337,f7635,f8331])).

fof(f8337,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK1)))
    | ~ spl206_45 ),
    inference(forward_demodulation,[],[f8238,f4635])).

fof(f8238,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(sK1,k1_xboole_0)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3491,f7637,f4620])).

fof(f8336,plain,
    ( spl206_76
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8239,f7635,f8331])).

fof(f8239,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK1)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f4948,f7637,f4620])).

fof(f8334,plain,
    ( spl206_76
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8241,f7635,f8331])).

fof(f8241,plain,
    ( r1_xboole_0(k1_xboole_0,k3_tarski(k2_tarski(k1_xboole_0,sK1)))
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f3491,f7637,f4620])).

fof(f8329,plain,
    ( spl206_75
    | ~ spl206_45 ),
    inference(avatar_split_clause,[],[f8242,f7635,f8326])).

fof(f8326,plain,
    ( spl206_75
  <=> k1_xboole_0 = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_75])])).

fof(f8242,plain,
    ( k1_xboole_0 = k4_xboole_0(k3_tarski(k2_tarski(k1_xboole_0,sK1)),sK1)
    | ~ spl206_45 ),
    inference(unit_resulting_resolution,[],[f7637,f4629])).

fof(f8053,plain,
    ( spl206_74
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5121,f5107,f8050])).

fof(f8050,plain,
    ( spl206_74
  <=> r1_tarski(k2_relat_1(sK6(sK1,k1_xboole_0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_74])])).

fof(f5121,plain,
    ( r1_tarski(k2_relat_1(sK6(sK1,k1_xboole_0)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f5109,f2768])).

fof(f2768,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1289])).

fof(f1289,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1288])).

fof(f1288,plain,(
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

fof(f8048,plain,
    ( spl206_73
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5126,f5107,f8045])).

fof(f8045,plain,
    ( spl206_73
  <=> r1_tarski(sK1,k1_zfmisc_1(k3_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_73])])).

fof(f5126,plain,
    ( r1_tarski(sK1,k1_zfmisc_1(k3_tarski(sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4083,f5109,f2768])).

fof(f8043,plain,
    ( ~ spl206_72
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5128,f5107,f8040])).

fof(f5128,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2786])).

fof(f2786,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1299])).

fof(f1299,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1125])).

fof(f1125,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f8038,plain,
    ( spl206_71
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5129,f5107,f8035])).

fof(f8035,plain,
    ( spl206_71
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_71])])).

fof(f5129,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2798])).

fof(f2798,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2216])).

fof(f8033,plain,
    ( ~ spl206_70
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5130,f5107,f8030])).

fof(f8030,plain,
    ( spl206_70
  <=> r2_hidden(sK177(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_70])])).

fof(f5130,plain,
    ( ~ r2_hidden(sK177(sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4021,f5109,f2803])).

fof(f8028,plain,
    ( spl206_69
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5131,f5107,f8025])).

fof(f8025,plain,
    ( spl206_69
  <=> r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_69])])).

fof(f5131,plain,
    ( r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2818])).

fof(f2818,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1309])).

fof(f1309,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f432])).

fof(f432,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f7966,plain,
    ( spl206_68
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5261,f5107,f7962])).

fof(f7962,plain,
    ( spl206_68
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_68])])).

fof(f5261,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f2980,f5109,f2831])).

fof(f2980,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f1240])).

fof(f1240,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f7965,plain,
    ( spl206_68
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5262,f5107,f7962])).

fof(f5262,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f2980,f5109,f2831])).

fof(f7960,plain,
    ( spl206_67
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5263,f5107,f7957])).

fof(f7957,plain,
    ( spl206_67
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_zfmisc_1(k3_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_67])])).

fof(f5263,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_zfmisc_1(k3_tarski(sK1)))))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4083,f2980,f5109,f2831])).

fof(f7955,plain,
    ( spl206_64
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5265,f5107,f7865])).

fof(f7865,plain,
    ( spl206_64
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_64])])).

fof(f5265,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2980,f5109,f2831])).

fof(f7946,plain,
    ( spl206_63
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5308,f5107,f7852])).

fof(f7852,plain,
    ( spl206_63
  <=> m1_subset_1(sK19(k2_zfmisc_1(sK1,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_63])])).

fof(f5308,plain,
    ( m1_subset_1(sK19(k2_zfmisc_1(sK1,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2869,f5109,f2831])).

fof(f7937,plain,
    ( spl206_62
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5351,f5107,f7839])).

fof(f7839,plain,
    ( spl206_62
  <=> m1_subset_1(sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_62])])).

fof(f5351,plain,
    ( m1_subset_1(sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2871,f5109,f2831])).

fof(f7879,plain,
    ( spl206_66
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5481,f5107,f7875])).

fof(f7875,plain,
    ( spl206_66
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_66])])).

fof(f5481,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f2980,f5109,f2831])).

fof(f7878,plain,
    ( spl206_66
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5482,f5107,f7875])).

fof(f5482,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f2980,f5109,f2831])).

fof(f7873,plain,
    ( spl206_65
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5483,f5107,f7870])).

fof(f7870,plain,
    ( spl206_65
  <=> m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_65])])).

fof(f5483,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_zfmisc_1(k3_tarski(sK1)),sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4083,f2980,f5109,f2831])).

fof(f7868,plain,
    ( spl206_64
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5485,f5107,f7865])).

fof(f5485,plain,
    ( m1_subset_1(k6_relat_1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2980,f5109,f2831])).

fof(f7855,plain,
    ( spl206_63
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5528,f5107,f7852])).

fof(f5528,plain,
    ( m1_subset_1(sK19(k2_zfmisc_1(sK1,sK1)),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2869,f5109,f2831])).

fof(f7842,plain,
    ( spl206_62
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5571,f5107,f7839])).

fof(f5571,plain,
    ( m1_subset_1(sK20(k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))),k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f2871,f5109,f2831])).

fof(f7829,plain,
    ( spl206_61
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5614,f5107,f7817])).

fof(f7817,plain,
    ( spl206_61
  <=> r1_tarski(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_61])])).

fof(f5614,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK2,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f2915])).

fof(f2915,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1374])).

fof(f1374,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1373])).

fof(f1373,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f335])).

fof(f335,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

fof(f7820,plain,
    ( spl206_61
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5657,f5107,f7817])).

fof(f5657,plain,
    ( r1_tarski(k2_zfmisc_1(sK1,sK1),k2_zfmisc_1(sK2,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f2915])).

fof(f7814,plain,
    ( spl206_60
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5673,f5107,f7766])).

fof(f7766,plain,
    ( spl206_60
  <=> k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_60])])).

fof(f5673,plain,
    ( k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f5109,f2987])).

fof(f2987,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f1410,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1409])).

fof(f1409,plain,(
    ! [X0,X1,X2] :
      ( ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
        & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1044])).

fof(f1044,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
          & k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_funct_1)).

fof(f7813,plain,
    ( spl206_58
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5674,f5107,f7756])).

fof(f7756,plain,
    ( spl206_58
  <=> k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_58])])).

fof(f5674,plain,
    ( k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f5109,f2987])).

fof(f7812,plain,
    ( spl206_57
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5691,f5107,f7751])).

fof(f7751,plain,
    ( spl206_57
  <=> k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_57])])).

fof(f5691,plain,
    ( k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f5109,f2988])).

fof(f2988,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,X0) = k7_relat_1(k7_relat_1(X2,X1),X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1410])).

fof(f7811,plain,
    ( spl206_55
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5692,f5107,f7741])).

fof(f7741,plain,
    ( spl206_55
  <=> k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_55])])).

fof(f5692,plain,
    ( k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f5109,f2988])).

fof(f7808,plain,
    ( spl206_54
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5724,f5107,f7734])).

fof(f7734,plain,
    ( spl206_54
  <=> r1_tarski(k7_relat_1(sK89,sK1),k7_relat_1(sK89,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_54])])).

fof(f5724,plain,
    ( r1_tarski(k7_relat_1(sK89,sK1),k7_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4882,f5109,f2990])).

fof(f7807,plain,
    ( spl206_53
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5725,f5107,f7729])).

fof(f7729,plain,
    ( spl206_53
  <=> r1_tarski(k7_relat_1(sK128,sK1),k7_relat_1(sK128,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_53])])).

fof(f5725,plain,
    ( r1_tarski(k7_relat_1(sK128,sK1),k7_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4882,f5109,f2990])).

fof(f7806,plain,
    ( spl206_52
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5726,f5107,f7724])).

fof(f7724,plain,
    ( spl206_52
  <=> r1_tarski(k7_relat_1(sK162,sK1),k7_relat_1(sK162,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_52])])).

fof(f5726,plain,
    ( r1_tarski(k7_relat_1(sK162,sK1),k7_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4882,f5109,f2990])).

fof(f7803,plain,
    ( spl206_54
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5759,f5107,f7734])).

fof(f5759,plain,
    ( r1_tarski(k7_relat_1(sK89,sK1),k7_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4881,f5109,f2990])).

fof(f7802,plain,
    ( spl206_53
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5760,f5107,f7729])).

fof(f5760,plain,
    ( r1_tarski(k7_relat_1(sK128,sK1),k7_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4881,f5109,f2990])).

fof(f7801,plain,
    ( spl206_52
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5761,f5107,f7724])).

fof(f5761,plain,
    ( r1_tarski(k7_relat_1(sK162,sK1),k7_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4881,f5109,f2990])).

fof(f7769,plain,
    ( spl206_60
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5849,f5107,f7766])).

fof(f5849,plain,
    ( k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f2994])).

fof(f7764,plain,
    ( spl206_59
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5850,f5107,f7761])).

fof(f7761,plain,
    ( spl206_59
  <=> k7_relat_1(sK128,sK1) = k7_relat_1(k7_relat_1(sK128,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_59])])).

fof(f5850,plain,
    ( k7_relat_1(sK128,sK1) = k7_relat_1(k7_relat_1(sK128,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f2994])).

fof(f7759,plain,
    ( spl206_58
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5851,f5107,f7756])).

fof(f5851,plain,
    ( k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f2994])).

fof(f7754,plain,
    ( spl206_57
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5870,f5107,f7751])).

fof(f5870,plain,
    ( k7_relat_1(sK89,sK1) = k7_relat_1(k7_relat_1(sK89,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f2995])).

fof(f7749,plain,
    ( spl206_56
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5871,f5107,f7746])).

fof(f7746,plain,
    ( spl206_56
  <=> k7_relat_1(sK128,sK1) = k7_relat_1(k7_relat_1(sK128,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_56])])).

fof(f5871,plain,
    ( k7_relat_1(sK128,sK1) = k7_relat_1(k7_relat_1(sK128,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f2995])).

fof(f7744,plain,
    ( spl206_55
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5872,f5107,f7741])).

fof(f5872,plain,
    ( k7_relat_1(sK162,sK1) = k7_relat_1(k7_relat_1(sK162,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f2995])).

fof(f7737,plain,
    ( spl206_54
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5891,f5107,f7734])).

fof(f5891,plain,
    ( r1_tarski(k7_relat_1(sK89,sK1),k7_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f2996])).

fof(f7732,plain,
    ( spl206_53
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5892,f5107,f7729])).

fof(f5892,plain,
    ( r1_tarski(k7_relat_1(sK128,sK1),k7_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f2996])).

fof(f7727,plain,
    ( spl206_52
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5893,f5107,f7724])).

fof(f5893,plain,
    ( r1_tarski(k7_relat_1(sK162,sK1),k7_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f2996])).

fof(f7722,plain,
    ( spl206_51
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5912,f5107,f7719])).

fof(f7719,plain,
    ( spl206_51
  <=> k9_relat_1(sK89,sK1) = k9_relat_1(k7_relat_1(sK89,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_51])])).

fof(f5912,plain,
    ( k9_relat_1(sK89,sK1) = k9_relat_1(k7_relat_1(sK89,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3045])).

fof(f7717,plain,
    ( spl206_50
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5913,f5107,f7714])).

fof(f7714,plain,
    ( spl206_50
  <=> k9_relat_1(sK128,sK1) = k9_relat_1(k7_relat_1(sK128,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_50])])).

fof(f5913,plain,
    ( k9_relat_1(sK128,sK1) = k9_relat_1(k7_relat_1(sK128,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3045])).

fof(f7712,plain,
    ( spl206_49
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5914,f5107,f7709])).

fof(f7709,plain,
    ( spl206_49
  <=> k9_relat_1(sK162,sK1) = k9_relat_1(k7_relat_1(sK162,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_49])])).

fof(f5914,plain,
    ( k9_relat_1(sK162,sK1) = k9_relat_1(k7_relat_1(sK162,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3045])).

fof(f7707,plain,
    ( spl206_48
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5919,f5107,f7703])).

fof(f7703,plain,
    ( spl206_48
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_48])])).

fof(f5919,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f3476])).

fof(f3476,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2448])).

fof(f2448,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f7706,plain,
    ( spl206_48
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5920,f5107,f7703])).

fof(f5920,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f3478])).

fof(f3478,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2449])).

fof(f2449,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f7678,plain,
    ( spl206_47
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f5963,f5107,f7663])).

fof(f7663,plain,
    ( spl206_47
  <=> r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_47])])).

fof(f5963,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f3635])).

fof(f3635,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1816])).

fof(f1816,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1815])).

fof(f1815,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f95])).

fof(f95,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k4_xboole_0(X0,X3),k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

fof(f7666,plain,
    ( spl206_47
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6006,f5107,f7663])).

fof(f6006,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK2),k4_xboole_0(sK2,sK1))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f3635])).

fof(f7658,plain,
    ( spl206_46
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6017,f5107,f7655])).

fof(f7655,plain,
    ( spl206_46
  <=> r1_xboole_0(sK1,k2_relat_1(sK6(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_46])])).

fof(f6017,plain,
    ( r1_xboole_0(sK1,k2_relat_1(sK6(k1_xboole_0,k1_xboole_0)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f3491,f5109,f3659])).

fof(f7647,plain,
    ( spl206_45
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6022,f5107,f7635])).

fof(f6022,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f4592,f5109,f3659])).

fof(f4592,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f3250,f3248])).

fof(f3250,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f162])).

fof(f162,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f7638,plain,
    ( spl206_45
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6030,f5107,f7635])).

fof(f6030,plain,
    ( r1_xboole_0(k1_xboole_0,sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f3658,f5109,f3659])).

fof(f3658,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f147])).

fof(f147,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f7632,plain,
    ( spl206_41
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6050,f5107,f7569])).

fof(f7569,plain,
    ( spl206_41
  <=> k8_relat_1(sK1,sK89) = k8_relat_1(sK2,k8_relat_1(sK1,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_41])])).

fof(f6050,plain,
    ( k8_relat_1(sK1,sK89) = k8_relat_1(sK2,k8_relat_1(sK1,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f5109,f3770])).

fof(f3770,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1885])).

fof(f1885,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
        & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1884])).

fof(f1884,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
        & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) )
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1051])).

fof(f1051,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r1_tarski(X0,X1)
       => ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
          & k8_relat_1(X0,X2) = k8_relat_1(X1,k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_funct_1)).

fof(f7631,plain,
    ( spl206_39
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6051,f5107,f7559])).

fof(f7559,plain,
    ( spl206_39
  <=> k8_relat_1(sK1,sK162) = k8_relat_1(sK2,k8_relat_1(sK1,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_39])])).

fof(f6051,plain,
    ( k8_relat_1(sK1,sK162) = k8_relat_1(sK2,k8_relat_1(sK1,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f5109,f3770])).

fof(f7630,plain,
    ( spl206_44
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6068,f5107,f7585])).

fof(f7585,plain,
    ( spl206_44
  <=> k8_relat_1(sK1,sK89) = k8_relat_1(sK1,k8_relat_1(sK2,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_44])])).

fof(f6068,plain,
    ( k8_relat_1(sK1,sK89) = k8_relat_1(sK1,k8_relat_1(sK2,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3463,f5109,f3771])).

fof(f3771,plain,(
    ! [X2,X0,X1] :
      ( k8_relat_1(X0,X2) = k8_relat_1(X0,k8_relat_1(X1,X2))
      | ~ r1_tarski(X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1885])).

fof(f7629,plain,
    ( spl206_42
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6069,f5107,f7575])).

fof(f7575,plain,
    ( spl206_42
  <=> k8_relat_1(sK1,sK162) = k8_relat_1(sK1,k8_relat_1(sK2,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_42])])).

fof(f6069,plain,
    ( k8_relat_1(sK1,sK162) = k8_relat_1(sK1,k8_relat_1(sK2,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3901,f5109,f3771])).

fof(f7626,plain,
    ( spl206_38
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6101,f5107,f7552])).

fof(f7552,plain,
    ( spl206_38
  <=> r1_tarski(k8_relat_1(sK1,sK89),k8_relat_1(sK2,sK89)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_38])])).

fof(f6101,plain,
    ( r1_tarski(k8_relat_1(sK1,sK89),k8_relat_1(sK2,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4882,f5109,f3773])).

fof(f7625,plain,
    ( spl206_37
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6102,f5107,f7547])).

fof(f7547,plain,
    ( spl206_37
  <=> r1_tarski(k8_relat_1(sK1,sK128),k8_relat_1(sK2,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_37])])).

fof(f6102,plain,
    ( r1_tarski(k8_relat_1(sK1,sK128),k8_relat_1(sK2,sK128))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4882,f5109,f3773])).

fof(f7624,plain,
    ( spl206_36
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6103,f5107,f7542])).

fof(f7542,plain,
    ( spl206_36
  <=> r1_tarski(k8_relat_1(sK1,sK162),k8_relat_1(sK2,sK162)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_36])])).

fof(f6103,plain,
    ( r1_tarski(k8_relat_1(sK1,sK162),k8_relat_1(sK2,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4882,f5109,f3773])).

fof(f7621,plain,
    ( spl206_38
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6136,f5107,f7552])).

fof(f6136,plain,
    ( r1_tarski(k8_relat_1(sK1,sK89),k8_relat_1(sK2,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4881,f5109,f3773])).

fof(f7620,plain,
    ( spl206_37
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6137,f5107,f7547])).

fof(f6137,plain,
    ( r1_tarski(k8_relat_1(sK1,sK128),k8_relat_1(sK2,sK128))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4881,f5109,f3773])).

fof(f7619,plain,
    ( spl206_36
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6138,f5107,f7542])).

fof(f6138,plain,
    ( r1_tarski(k8_relat_1(sK1,sK162),k8_relat_1(sK2,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4881,f5109,f3773])).

fof(f7588,plain,
    ( spl206_44
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6226,f5107,f7585])).

fof(f6226,plain,
    ( k8_relat_1(sK1,sK89) = k8_relat_1(sK1,k8_relat_1(sK2,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3774])).

fof(f7583,plain,
    ( spl206_43
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6227,f5107,f7580])).

fof(f7580,plain,
    ( spl206_43
  <=> k8_relat_1(sK1,sK128) = k8_relat_1(sK1,k8_relat_1(sK2,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_43])])).

fof(f6227,plain,
    ( k8_relat_1(sK1,sK128) = k8_relat_1(sK1,k8_relat_1(sK2,sK128))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3774])).

fof(f7578,plain,
    ( spl206_42
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6228,f5107,f7575])).

fof(f6228,plain,
    ( k8_relat_1(sK1,sK162) = k8_relat_1(sK1,k8_relat_1(sK2,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3774])).

fof(f7572,plain,
    ( spl206_41
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6247,f5107,f7569])).

fof(f6247,plain,
    ( k8_relat_1(sK1,sK89) = k8_relat_1(sK2,k8_relat_1(sK1,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3775])).

fof(f7567,plain,
    ( spl206_40
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6248,f5107,f7564])).

fof(f7564,plain,
    ( spl206_40
  <=> k8_relat_1(sK1,sK128) = k8_relat_1(sK2,k8_relat_1(sK1,sK128)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_40])])).

fof(f6248,plain,
    ( k8_relat_1(sK1,sK128) = k8_relat_1(sK2,k8_relat_1(sK1,sK128))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3775])).

fof(f7562,plain,
    ( spl206_39
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6249,f5107,f7559])).

fof(f6249,plain,
    ( k8_relat_1(sK1,sK162) = k8_relat_1(sK2,k8_relat_1(sK1,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3775])).

fof(f7555,plain,
    ( spl206_38
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6268,f5107,f7552])).

fof(f6268,plain,
    ( r1_tarski(k8_relat_1(sK1,sK89),k8_relat_1(sK2,sK89))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3776])).

fof(f7550,plain,
    ( spl206_37
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6269,f5107,f7547])).

fof(f6269,plain,
    ( r1_tarski(k8_relat_1(sK1,sK128),k8_relat_1(sK2,sK128))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3776])).

fof(f7545,plain,
    ( spl206_36
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6270,f5107,f7542])).

fof(f6270,plain,
    ( r1_tarski(k8_relat_1(sK1,sK162),k8_relat_1(sK2,sK162))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3776])).

fof(f7538,plain,
    ( spl206_35
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6303,f5107,f7495])).

fof(f7495,plain,
    ( spl206_35
  <=> r1_tarski(k10_relat_1(sK89,sK1),k10_relat_1(sK89,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_35])])).

fof(f6303,plain,
    ( r1_tarski(k10_relat_1(sK89,sK1),k10_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4882,f5109,f3871])).

fof(f7537,plain,
    ( spl206_34
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6304,f5107,f7490])).

fof(f7490,plain,
    ( spl206_34
  <=> r1_tarski(k10_relat_1(sK128,sK1),k10_relat_1(sK128,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_34])])).

fof(f6304,plain,
    ( r1_tarski(k10_relat_1(sK128,sK1),k10_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4882,f5109,f3871])).

fof(f7536,plain,
    ( spl206_33
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6305,f5107,f7485])).

fof(f7485,plain,
    ( spl206_33
  <=> r1_tarski(k10_relat_1(sK162,sK1),k10_relat_1(sK162,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_33])])).

fof(f6305,plain,
    ( r1_tarski(k10_relat_1(sK162,sK1),k10_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4882,f5109,f3871])).

fof(f7533,plain,
    ( spl206_35
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6338,f5107,f7495])).

fof(f6338,plain,
    ( r1_tarski(k10_relat_1(sK89,sK1),k10_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4881,f5109,f3871])).

fof(f7532,plain,
    ( spl206_34
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6339,f5107,f7490])).

fof(f6339,plain,
    ( r1_tarski(k10_relat_1(sK128,sK1),k10_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4881,f5109,f3871])).

fof(f7531,plain,
    ( spl206_33
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6340,f5107,f7485])).

fof(f6340,plain,
    ( r1_tarski(k10_relat_1(sK162,sK1),k10_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4881,f5109,f3871])).

fof(f7498,plain,
    ( spl206_35
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6428,f5107,f7495])).

fof(f6428,plain,
    ( r1_tarski(k10_relat_1(sK89,sK1),k10_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3872])).

fof(f7493,plain,
    ( spl206_34
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6429,f5107,f7490])).

fof(f6429,plain,
    ( r1_tarski(k10_relat_1(sK128,sK1),k10_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3872])).

fof(f7488,plain,
    ( spl206_33
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6430,f5107,f7485])).

fof(f6430,plain,
    ( r1_tarski(k10_relat_1(sK162,sK1),k10_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3872])).

fof(f7481,plain,
    ( spl206_32
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6463,f5107,f7438])).

fof(f7438,plain,
    ( spl206_32
  <=> r1_tarski(k9_relat_1(sK89,sK1),k9_relat_1(sK89,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_32])])).

fof(f6463,plain,
    ( r1_tarski(k9_relat_1(sK89,sK1),k9_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4882,f5109,f3893])).

fof(f7480,plain,
    ( spl206_31
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6464,f5107,f7433])).

fof(f7433,plain,
    ( spl206_31
  <=> r1_tarski(k9_relat_1(sK128,sK1),k9_relat_1(sK128,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_31])])).

fof(f6464,plain,
    ( r1_tarski(k9_relat_1(sK128,sK1),k9_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4882,f5109,f3893])).

fof(f7479,plain,
    ( spl206_30
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6465,f5107,f7428])).

fof(f7428,plain,
    ( spl206_30
  <=> r1_tarski(k9_relat_1(sK162,sK1),k9_relat_1(sK162,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_30])])).

fof(f6465,plain,
    ( r1_tarski(k9_relat_1(sK162,sK1),k9_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4882,f5109,f3893])).

fof(f7476,plain,
    ( spl206_32
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6498,f5107,f7438])).

fof(f6498,plain,
    ( r1_tarski(k9_relat_1(sK89,sK1),k9_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f3462,f4881,f5109,f3893])).

fof(f7475,plain,
    ( spl206_31
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6499,f5107,f7433])).

fof(f6499,plain,
    ( r1_tarski(k9_relat_1(sK128,sK1),k9_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f3572,f4881,f5109,f3893])).

fof(f7474,plain,
    ( spl206_30
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6500,f5107,f7428])).

fof(f6500,plain,
    ( r1_tarski(k9_relat_1(sK162,sK1),k9_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f3900,f4881,f5109,f3893])).

fof(f7441,plain,
    ( spl206_32
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6588,f5107,f7438])).

fof(f6588,plain,
    ( r1_tarski(k9_relat_1(sK89,sK1),k9_relat_1(sK89,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3894])).

fof(f7436,plain,
    ( spl206_31
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6589,f5107,f7433])).

fof(f6589,plain,
    ( r1_tarski(k9_relat_1(sK128,sK1),k9_relat_1(sK128,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3894])).

fof(f7431,plain,
    ( spl206_30
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6590,f5107,f7428])).

fof(f6590,plain,
    ( r1_tarski(k9_relat_1(sK162,sK1),k9_relat_1(sK162,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3894])).

fof(f7426,plain,
    ( spl206_29
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6595,f5107,f7423])).

fof(f7423,plain,
    ( spl206_29
  <=> k2_wellord1(k1_xboole_0,sK1) = k2_wellord1(k2_wellord1(k1_xboole_0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_29])])).

fof(f6595,plain,
    ( k2_wellord1(k1_xboole_0,sK1) = k2_wellord1(k2_wellord1(k1_xboole_0,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4298,f5109,f3930])).

fof(f7421,plain,
    ( spl206_28
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6609,f5107,f7418])).

fof(f7418,plain,
    ( spl206_28
  <=> k2_wellord1(sK89,sK1) = k2_wellord1(k2_wellord1(sK89,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_28])])).

fof(f6609,plain,
    ( k2_wellord1(sK89,sK1) = k2_wellord1(k2_wellord1(sK89,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f3930])).

fof(f7416,plain,
    ( spl206_27
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6610,f5107,f7413])).

fof(f7413,plain,
    ( spl206_27
  <=> k2_wellord1(sK128,sK1) = k2_wellord1(k2_wellord1(sK128,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_27])])).

fof(f6610,plain,
    ( k2_wellord1(sK128,sK1) = k2_wellord1(k2_wellord1(sK128,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f3930])).

fof(f7411,plain,
    ( spl206_26
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6611,f5107,f7408])).

fof(f7408,plain,
    ( spl206_26
  <=> k2_wellord1(sK162,sK1) = k2_wellord1(k2_wellord1(sK162,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_26])])).

fof(f6611,plain,
    ( k2_wellord1(sK162,sK1) = k2_wellord1(k2_wellord1(sK162,sK2),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f3930])).

fof(f7405,plain,
    ( spl206_25
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6617,f5107,f7394])).

fof(f7394,plain,
    ( spl206_25
  <=> r1_tarski(k5_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_25])])).

fof(f6617,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4044])).

fof(f4044,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2089])).

fof(f2089,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2088])).

fof(f2088,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f7404,plain,
    ( spl206_25
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6618,f5107,f7394])).

fof(f6618,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4044])).

fof(f7403,plain,
    ( spl206_24
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7402,f5107,f7388])).

fof(f7388,plain,
    ( spl206_24
  <=> r1_tarski(k5_xboole_0(k1_xboole_0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_24])])).

fof(f7402,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,sK1),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6619,f4059])).

fof(f6619,plain,
    ( r1_tarski(k5_xboole_0(sK1,k1_xboole_0),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f5109,f4044])).

fof(f7401,plain,
    ( spl206_23
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6622,f5107,f7381])).

fof(f7381,plain,
    ( spl206_23
  <=> r1_tarski(k5_xboole_0(sK1,k2_relat_1(sK6(sK2,k1_xboole_0))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_23])])).

fof(f6622,plain,
    ( r1_tarski(k5_xboole_0(sK1,k2_relat_1(sK6(sK2,k1_xboole_0))),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f5109,f4044])).

fof(f7399,plain,
    ( spl206_25
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7398,f5107,f7394])).

fof(f7398,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6626,f4059])).

fof(f6626,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4044])).

fof(f7397,plain,
    ( spl206_25
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7392,f5107,f7394])).

fof(f7392,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6627,f4059])).

fof(f6627,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4044])).

fof(f7391,plain,
    ( spl206_24
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6628,f5107,f7388])).

fof(f6628,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f5109,f4044])).

fof(f7384,plain,
    ( spl206_23
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7379,f5107,f7381])).

fof(f7379,plain,
    ( r1_tarski(k5_xboole_0(sK1,k2_relat_1(sK6(sK2,k1_xboole_0))),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6631,f4059])).

fof(f6631,plain,
    ( r1_tarski(k5_xboole_0(k2_relat_1(sK6(sK2,k1_xboole_0)),sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f5109,f4044])).

fof(f7376,plain,
    ( spl206_22
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6634,f5107,f7373])).

fof(f7373,plain,
    ( spl206_22
  <=> r1_tarski(k3_tarski(sK1),k3_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_22])])).

fof(f6634,plain,
    ( r1_tarski(k3_tarski(sK1),k3_tarski(sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f4071])).

fof(f4071,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2093])).

fof(f2093,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f444])).

fof(f444,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f7356,plain,
    ( spl206_21
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7351,f5107,f7353])).

fof(f7353,plain,
    ( spl206_21
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK89,k7_relat_1(sK89,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_21])])).

fof(f7351,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK89,k7_relat_1(sK89,sK2)),sK1)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6649,f4247])).

fof(f6649,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK89,k7_relat_1(sK89,sK2)),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3462,f5109,f4242])).

fof(f7350,plain,
    ( spl206_20
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7345,f5107,f7347])).

fof(f7347,plain,
    ( spl206_20
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK128,k7_relat_1(sK128,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_20])])).

fof(f7345,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK128,k7_relat_1(sK128,sK2)),sK1)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6650,f4247])).

fof(f6650,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK128,k7_relat_1(sK128,sK2)),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3572,f5109,f4242])).

fof(f7344,plain,
    ( spl206_19
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7339,f5107,f7341])).

fof(f7341,plain,
    ( spl206_19
  <=> k1_xboole_0 = k7_relat_1(k4_xboole_0(sK162,k7_relat_1(sK162,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_19])])).

fof(f7339,plain,
    ( k1_xboole_0 = k7_relat_1(k4_xboole_0(sK162,k7_relat_1(sK162,sK2)),sK1)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6651,f4247])).

fof(f6651,plain,
    ( k1_xboole_0 = k7_relat_1(k6_subset_1(sK162,k7_relat_1(sK162,sK2)),sK1)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3900,f5109,f4242])).

fof(f7334,plain,
    ( spl206_18
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6659,f5107,f7331])).

fof(f7331,plain,
    ( spl206_18
  <=> v5_relat_1(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_18])])).

fof(f6659,plain,
    ( v5_relat_1(k6_relat_1(sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3831,f3824,f5109,f4279])).

fof(f7329,plain,
    ( spl206_17
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6662,f5107,f7325])).

fof(f7325,plain,
    ( spl206_17
  <=> v5_relat_1(sK204(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_17])])).

fof(f6662,plain,
    ( v5_relat_1(sK204(sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4290,f4291,f5109,f4279])).

fof(f7328,plain,
    ( spl206_17
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6666,f5107,f7325])).

fof(f6666,plain,
    ( v5_relat_1(sK204(sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4292,f4290,f4293,f4291,f5109,f4281])).

fof(f4281,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_ordinal1(X2)
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2182])).

fof(f2182,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) )
          | ~ v5_ordinal1(X2)
          | ~ v1_funct_1(X2)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2181])).

fof(f2181,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) )
          | ~ v5_ordinal1(X2)
          | ~ v1_funct_1(X2)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1116])).

fof(f1116,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => ( v5_ordinal1(X2)
            & v1_funct_1(X2)
            & v5_relat_1(X2,X1)
            & v1_relat_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_ordinal1)).

fof(f4293,plain,(
    ! [X0] : v5_ordinal1(sK204(X0)) ),
    inference(cnf_transformation,[],[f2743])).

fof(f4292,plain,(
    ! [X0] : v1_funct_1(sK204(X0)) ),
    inference(cnf_transformation,[],[f2743])).

fof(f7323,plain,
    ( spl206_16
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6669,f5107,f7320])).

fof(f7320,plain,
    ( spl206_16
  <=> v4_relat_1(k6_relat_1(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_16])])).

fof(f6669,plain,
    ( v4_relat_1(k6_relat_1(sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f3831,f3823,f5109,f4310])).

fof(f7318,plain,
    ( spl206_15
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6672,f5107,f7315])).

fof(f7315,plain,
    ( spl206_15
  <=> v4_relat_1(sK205(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_15])])).

fof(f6672,plain,
    ( v4_relat_1(sK205(sK1),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4314,f4316,f5109,f4310])).

fof(f7097,plain,
    ( spl206_14
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6846,f5107,f7086])).

fof(f7086,plain,
    ( spl206_14
  <=> r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_14])])).

fof(f6846,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4337])).

fof(f4337,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2766,f3631])).

fof(f2766,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1285])).

fof(f1285,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1284])).

fof(f1284,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f161])).

fof(f161,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f7096,plain,
    ( spl206_14
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6847,f5107,f7086])).

fof(f6847,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4337])).

fof(f7095,plain,
    ( spl206_13
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7094,f5107,f7080])).

fof(f7080,plain,
    ( spl206_13
  <=> r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_13])])).

fof(f7094,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,sK1)),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6848,f4635])).

fof(f6848,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,k1_xboole_0)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f5109,f4337])).

fof(f7093,plain,
    ( spl206_12
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6851,f5107,f7073])).

fof(f7073,plain,
    ( spl206_12
  <=> r1_tarski(k3_tarski(k2_tarski(sK1,k2_relat_1(sK6(sK2,k1_xboole_0)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_12])])).

fof(f6851,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,k2_relat_1(sK6(sK2,k1_xboole_0)))),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f5109,f4337])).

fof(f7091,plain,
    ( spl206_14
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7090,f5107,f7086])).

fof(f7090,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6855,f4635])).

fof(f6855,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK1)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4337])).

fof(f7089,plain,
    ( spl206_14
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7084,f5107,f7086])).

fof(f7084,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,sK2)),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6856,f4635])).

fof(f6856,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK2,sK1)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4337])).

fof(f7083,plain,
    ( spl206_13
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6857,f5107,f7080])).

fof(f6857,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k1_xboole_0,sK1)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f2830,f5109,f4337])).

fof(f7076,plain,
    ( spl206_12
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7071,f5107,f7073])).

fof(f7071,plain,
    ( r1_tarski(k3_tarski(k2_tarski(sK1,k2_relat_1(sK6(sK2,k1_xboole_0)))),sK2)
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6860,f4635])).

fof(f6860,plain,
    ( r1_tarski(k3_tarski(k2_tarski(k2_relat_1(sK6(sK2,k1_xboole_0)),sK1)),sK2)
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4871,f5109,f4337])).

fof(f7068,plain,
    ( spl206_11
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7067,f5107,f7057])).

fof(f7057,plain,
    ( spl206_11
  <=> r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_11])])).

fof(f7067,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6863,f4596])).

fof(f6863,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4338])).

fof(f4338,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2767,f3248])).

fof(f2767,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1287])).

fof(f1287,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1286])).

fof(f1286,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f75])).

fof(f75,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f7066,plain,
    ( spl206_11
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7065,f5107,f7057])).

fof(f7065,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6864,f4596])).

fof(f6864,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4338])).

fof(f7064,plain,
    ( spl206_10
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6865,f5107,f7052])).

fof(f7052,plain,
    ( spl206_10
  <=> r1_tarski(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_zfmisc_1(k3_tarski(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_10])])).

fof(f6865,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_zfmisc_1(k3_tarski(sK1)))))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4083,f5109,f4338])).

fof(f7061,plain,
    ( spl206_11
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6868,f5107,f7057])).

fof(f6868,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4882,f5109,f4338])).

fof(f7060,plain,
    ( spl206_11
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6869,f5107,f7057])).

fof(f6869,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4881,f5109,f4338])).

fof(f7055,plain,
    ( spl206_10
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f7050,f5107,f7052])).

fof(f7050,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k4_xboole_0(sK2,k1_zfmisc_1(k3_tarski(sK1)))))
    | ~ spl206_2 ),
    inference(forward_demodulation,[],[f6870,f4596])).

fof(f6870,plain,
    ( r1_tarski(sK1,k4_xboole_0(k1_zfmisc_1(k3_tarski(sK1)),k4_xboole_0(k1_zfmisc_1(k3_tarski(sK1)),sK2)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4083,f5109,f4338])).

fof(f7044,plain,
    ( spl206_9
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6878,f5107,f7041])).

fof(f7041,plain,
    ( spl206_9
  <=> sK2 = k3_tarski(k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_9])])).

fof(f6878,plain,
    ( sK2 = k3_tarski(k2_tarski(sK1,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f4362])).

fof(f4362,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2819,f3631])).

fof(f2819,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1310])).

fof(f1310,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f7039,plain,
    ( spl206_8
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6879,f5107,f7036])).

fof(f7036,plain,
    ( spl206_8
  <=> sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_8])])).

fof(f6879,plain,
    ( sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f4363])).

fof(f4363,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2820,f3248])).

fof(f2820,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1311])).

fof(f1311,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f7013,plain,
    ( spl206_7
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6922,f5107,f6988])).

fof(f6988,plain,
    ( spl206_7
  <=> k2_zfmisc_1(sK1,sK1) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_7])])).

fof(f6922,plain,
    ( k2_zfmisc_1(sK1,sK1) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f4393])).

fof(f4393,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X2) = k4_xboole_0(k2_zfmisc_1(X0,X3),k4_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f2914,f3248])).

fof(f2914,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1372])).

fof(f1372,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f1371])).

fof(f1371,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f340])).

fof(f340,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f6991,plain,
    ( spl206_7
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6965,f5107,f6988])).

fof(f6965,plain,
    ( k2_zfmisc_1(sK1,sK1) = k4_xboole_0(k2_zfmisc_1(sK1,sK2),k4_xboole_0(k2_zfmisc_1(sK1,sK2),k2_zfmisc_1(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f5109,f4393])).

fof(f6986,plain,
    ( spl206_6
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6966,f5107,f6982])).

fof(f6982,plain,
    ( spl206_6
  <=> r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK177(sK1),sK177(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_6])])).

fof(f6966,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK177(sK1),sK177(sK1))))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4021,f5109,f4493])).

fof(f6985,plain,
    ( spl206_6
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6967,f5107,f6982])).

fof(f6967,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK2,k2_tarski(sK177(sK1),sK177(sK1))))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f4021,f5109,f4494])).

fof(f6980,plain,
    ( spl206_5
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6969,f5107,f6977])).

fof(f6977,plain,
    ( spl206_5
  <=> sK2 = k3_tarski(k2_tarski(sK1,k4_xboole_0(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_5])])).

fof(f6969,plain,
    ( sK2 = k3_tarski(k2_tarski(sK1,k4_xboole_0(sK2,sK1)))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f4628])).

fof(f4628,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f3286,f3631])).

fof(f3286,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1616])).

fof(f1616,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f107])).

fof(f107,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f6975,plain,
    ( spl206_4
    | ~ spl206_2 ),
    inference(avatar_split_clause,[],[f6970,f5107,f6972])).

fof(f6972,plain,
    ( spl206_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl206_4])])).

fof(f6970,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK2))
    | ~ spl206_2 ),
    inference(unit_resulting_resolution,[],[f5109,f4879])).

fof(f4879,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f2800])).

fof(f2800,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2220])).

fof(f2220,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK7(X0,X1),X0)
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( r1_tarski(sK7(X0,X1),X0)
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f2218,f2219])).

fof(f2219,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK7(X0,X1),X0)
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( r1_tarski(sK7(X0,X1),X0)
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2218,plain,(
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
    inference(rectify,[],[f2217])).

fof(f2217,plain,(
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

fof(f5115,plain,(
    spl206_3 ),
    inference(avatar_split_clause,[],[f2747,f5112])).

fof(f2747,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f2202])).

fof(f2202,plain,
    ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f1264,f2201])).

fof(f2201,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
   => ( ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3)
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f1264,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f1263])).

fof(f1263,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3)
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f1246])).

fof(f1246,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
       => ( r1_tarski(X1,X2)
         => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    inference(negated_conjecture,[],[f1245])).

fof(f1245,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(X1,X2)
       => r2_relset_1(X1,X0,k5_relset_1(X1,X0,X3,X2),X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_relset_1)).

fof(f5110,plain,(
    spl206_2 ),
    inference(avatar_split_clause,[],[f2748,f5107])).

fof(f2748,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f2202])).

fof(f5105,plain,(
    ~ spl206_1 ),
    inference(avatar_split_clause,[],[f2749,f5102])).

fof(f2749,plain,(
    ~ r2_relset_1(sK1,sK0,k5_relset_1(sK1,sK0,sK3,sK2),sK3) ),
    inference(cnf_transformation,[],[f2202])).
%------------------------------------------------------------------------------
