%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t9_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:58 EDT 2019

% Result     : Theorem 0.60s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       : 1298 (4571 expanded)
%              Number of leaves         :  358 (1897 expanded)
%              Depth                    :   10
%              Number of atoms          : 3339 (12175 expanded)
%              Number of equality atoms :   30 ( 134 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3911,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f405,f412,f419,f426,f433,f440,f447,f454,f461,f468,f475,f482,f489,f496,f503,f510,f517,f524,f531,f538,f545,f552,f559,f566,f573,f580,f587,f594,f601,f608,f615,f622,f629,f636,f643,f650,f659,f671,f680,f690,f700,f726,f739,f777,f787,f797,f804,f814,f824,f834,f853,f863,f885,f893,f901,f917,f925,f933,f941,f956,f964,f986,f994,f1001,f1009,f1017,f1025,f1050,f1057,f1065,f1082,f1092,f1105,f1113,f1120,f1140,f1148,f1162,f1191,f1199,f1210,f1224,f1232,f1245,f1253,f1266,f1274,f1275,f1282,f1300,f1302,f1310,f1317,f1324,f1337,f1345,f1369,f1377,f1384,f1397,f1400,f1407,f1429,f1437,f1457,f1466,f1474,f1482,f1507,f1515,f1522,f1531,f1539,f1547,f1555,f1558,f1565,f1589,f1597,f1604,f1612,f1620,f1628,f1636,f1644,f1670,f1678,f1685,f1693,f1701,f1709,f1717,f1725,f1764,f1772,f1779,f1787,f1809,f1817,f1824,f1832,f1842,f1868,f1877,f1887,f1896,f1906,f1915,f1925,f1934,f1945,f1954,f1962,f1982,f1990,f1997,f2005,f2027,f2035,f2042,f2060,f2168,f2173,f2197,f2208,f2244,f2255,f2266,f2277,f2288,f2299,f2327,f2338,f2349,f2360,f2371,f2410,f2421,f2432,f2467,f2479,f2491,f2503,f2514,f2536,f2547,f2594,f2597,f2604,f2616,f2623,f2647,f2658,f2669,f2680,f2698,f2709,f2720,f2731,f2759,f2770,f2781,f2792,f2803,f2814,f2825,f2836,f2849,f2861,f2879,f2887,f2906,f2916,f2937,f2947,f2968,f2978,f3017,f3027,f3048,f3058,f3069,f3079,f3098,f3106,f3143,f3151,f3170,f3178,f3197,f3205,f3224,f3232,f3271,f3279,f3298,f3306,f3325,f3333,f3352,f3360,f3380,f3388,f3471,f3479,f3497,f3505,f3524,f3532,f3619,f3629,f3637,f3645,f3653,f3661,f3669,f3677,f3685,f3693,f3701,f3711,f3722,f3733,f3745,f3756,f3779,f3787,f3807,f3815,f3835,f3843,f3850,f3859,f3873,f3880,f3899,f3902])).

fof(f3902,plain,
    ( spl28_1
    | ~ spl28_4
    | ~ spl28_416 ),
    inference(avatar_contradiction_clause,[],[f3901])).

fof(f3901,plain,
    ( $false
    | ~ spl28_1
    | ~ spl28_4
    | ~ spl28_416 ),
    inference(subsumption_resolution,[],[f3900,f404])).

fof(f404,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl28_1 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl28_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_1])])).

fof(f3900,plain,
    ( v2_struct_0(sK0)
    | ~ spl28_4
    | ~ spl28_416 ),
    inference(subsumption_resolution,[],[f3883,f418])).

fof(f418,plain,
    ( l1_struct_0(sK0)
    | ~ spl28_4 ),
    inference(avatar_component_clause,[],[f417])).

fof(f417,plain,
    ( spl28_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_4])])).

fof(f3883,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl28_416 ),
    inference(resolution,[],[f2842,f299])).

fof(f299,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f88])).

fof(f88,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',fc2_struct_0)).

fof(f2842,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl28_416 ),
    inference(avatar_component_clause,[],[f2841])).

fof(f2841,plain,
    ( spl28_416
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_416])])).

fof(f3899,plain,
    ( spl28_3
    | ~ spl28_4
    | ~ spl28_416 ),
    inference(avatar_contradiction_clause,[],[f3898])).

fof(f3898,plain,
    ( $false
    | ~ spl28_3
    | ~ spl28_4
    | ~ spl28_416 ),
    inference(subsumption_resolution,[],[f3897,f418])).

fof(f3897,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl28_3
    | ~ spl28_416 ),
    inference(subsumption_resolution,[],[f3882,f411])).

fof(f411,plain,
    ( ~ v7_struct_0(sK0)
    | ~ spl28_3 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl28_3
  <=> ~ v7_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_3])])).

fof(f3882,plain,
    ( v7_struct_0(sK0)
    | ~ l1_struct_0(sK0)
    | ~ spl28_416 ),
    inference(resolution,[],[f2842,f701])).

fof(f701,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | v7_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(resolution,[],[f298,f263])).

fof(f263,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
     => ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc1_realset1)).

fof(f298,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f137])).

fof(f137,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',fc6_struct_0)).

fof(f3880,plain,
    ( spl28_3
    | ~ spl28_4
    | ~ spl28_552 ),
    inference(avatar_contradiction_clause,[],[f3879])).

fof(f3879,plain,
    ( $false
    | ~ spl28_3
    | ~ spl28_4
    | ~ spl28_552 ),
    inference(subsumption_resolution,[],[f3878,f411])).

fof(f3878,plain,
    ( v7_struct_0(sK0)
    | ~ spl28_4
    | ~ spl28_552 ),
    inference(subsumption_resolution,[],[f3875,f418])).

fof(f3875,plain,
    ( ~ l1_struct_0(sK0)
    | v7_struct_0(sK0)
    | ~ spl28_552 ),
    inference(resolution,[],[f3872,f298])).

fof(f3872,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl28_552 ),
    inference(avatar_component_clause,[],[f3871])).

fof(f3871,plain,
    ( spl28_552
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_552])])).

fof(f3873,plain,
    ( spl28_552
    | spl28_421
    | ~ spl28_550 ),
    inference(avatar_split_clause,[],[f3864,f3857,f2859,f3871])).

fof(f2859,plain,
    ( spl28_421
  <=> ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_421])])).

fof(f3857,plain,
    ( spl28_550
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_550])])).

fof(f3864,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl28_421
    | ~ spl28_550 ),
    inference(subsumption_resolution,[],[f3863,f2860])).

fof(f2860,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl28_421 ),
    inference(avatar_component_clause,[],[f2859])).

fof(f3863,plain,
    ( v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl28_550 ),
    inference(subsumption_resolution,[],[f3860,f261])).

fof(f261,plain,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,axiom,(
    ! [X0] : v1_zfmisc_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',fc2_zfmisc_1)).

fof(f3860,plain,
    ( ~ v1_zfmisc_1(k1_tarski(sK1))
    | v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl28_550 ),
    inference(resolution,[],[f3858,f387])).

fof(f387,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_zfmisc_1(X1)
      | v1_subset_1(X1,X0)
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f386,f263])).

fof(f386,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f307,f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f104])).

fof(f104,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f43])).

fof(f43,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_xboole_0(X1)
           => v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc3_subset_1)).

fof(f307,plain,(
    ! [X0,X1] :
      ( v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f148])).

fof(f148,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_subset_1(X1,X0)
            & ~ v1_xboole_0(X1) )
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f147])).

fof(f147,plain,(
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
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc4_tex_2)).

fof(f3858,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl28_550 ),
    inference(avatar_component_clause,[],[f3857])).

fof(f3859,plain,
    ( spl28_550
    | ~ spl28_418
    | ~ spl28_548 ),
    inference(avatar_split_clause,[],[f3851,f3848,f2847,f3857])).

fof(f2847,plain,
    ( spl28_418
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_418])])).

fof(f3848,plain,
    ( spl28_548
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_548])])).

fof(f3851,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl28_418
    | ~ spl28_548 ),
    inference(forward_demodulation,[],[f3849,f2848])).

fof(f2848,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl28_418 ),
    inference(avatar_component_clause,[],[f2847])).

fof(f3849,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl28_548 ),
    inference(avatar_component_clause,[],[f3848])).

fof(f3850,plain,
    ( spl28_416
    | spl28_548
    | ~ spl28_70 ),
    inference(avatar_split_clause,[],[f2373,f648,f3848,f2841])).

fof(f648,plain,
    ( spl28_70
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_70])])).

fof(f2373,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl28_70 ),
    inference(resolution,[],[f349,f649])).

fof(f649,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl28_70 ),
    inference(avatar_component_clause,[],[f648])).

fof(f349,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f190])).

fof(f190,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f189])).

fof(f189,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f79])).

fof(f79,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',dt_k6_domain_1)).

fof(f3843,plain,
    ( spl28_546
    | ~ spl28_212 ),
    inference(avatar_split_clause,[],[f3825,f1405,f3841])).

fof(f3841,plain,
    ( spl28_546
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK24)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_546])])).

fof(f1405,plain,
    ( spl28_212
  <=> v1_relat_1(sK3(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_212])])).

fof(f3825,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK24))))
    | ~ spl28_212 ),
    inference(resolution,[],[f1430,f340])).

fof(f340,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(cnf_transformation,[],[f216])).

fof(f216,plain,(
    ! [X0] : m1_subset_1(sK10(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f77,f215])).

fof(f215,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK10(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f77,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',existence_m1_subset_1)).

fof(f1430,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK24)))
        | v1_relat_1(X0) )
    | ~ spl28_212 ),
    inference(resolution,[],[f1406,f287])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f126])).

fof(f126,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc2_relat_1)).

fof(f1406,plain,
    ( v1_relat_1(sK3(sK24))
    | ~ spl28_212 ),
    inference(avatar_component_clause,[],[f1405])).

fof(f3835,plain,
    ( spl28_544
    | ~ spl28_212 ),
    inference(avatar_split_clause,[],[f3827,f1405,f3833])).

fof(f3833,plain,
    ( spl28_544
  <=> v1_relat_1(sK12(sK3(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_544])])).

fof(f3827,plain,
    ( v1_relat_1(sK12(sK3(sK24)))
    | ~ spl28_212 ),
    inference(resolution,[],[f1430,f343])).

fof(f343,plain,(
    ! [X0] : m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f220])).

fof(f220,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK12(X0),X0)
      & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f67,f219])).

fof(f219,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK12(X0),X0)
        & m1_subset_1(sK12(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc3_subset_1)).

fof(f3815,plain,
    ( spl28_542
    | ~ spl28_208 ),
    inference(avatar_split_clause,[],[f3797,f1382,f3813])).

fof(f3813,plain,
    ( spl28_542
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK2(sK24)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_542])])).

fof(f1382,plain,
    ( spl28_208
  <=> v1_relat_1(sK2(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_208])])).

fof(f3797,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK2(sK24))))
    | ~ spl28_208 ),
    inference(resolution,[],[f1398,f340])).

fof(f1398,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK24)))
        | v1_relat_1(X0) )
    | ~ spl28_208 ),
    inference(resolution,[],[f1383,f287])).

fof(f1383,plain,
    ( v1_relat_1(sK2(sK24))
    | ~ spl28_208 ),
    inference(avatar_component_clause,[],[f1382])).

fof(f3807,plain,
    ( spl28_540
    | ~ spl28_208 ),
    inference(avatar_split_clause,[],[f3799,f1382,f3805])).

fof(f3805,plain,
    ( spl28_540
  <=> v1_relat_1(sK12(sK2(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_540])])).

fof(f3799,plain,
    ( v1_relat_1(sK12(sK2(sK24)))
    | ~ spl28_208 ),
    inference(resolution,[],[f1398,f343])).

fof(f3787,plain,
    ( spl28_538
    | ~ spl28_204 ),
    inference(avatar_split_clause,[],[f3769,f1367,f3785])).

fof(f3785,plain,
    ( spl28_538
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK24)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_538])])).

fof(f1367,plain,
    ( spl28_204
  <=> v1_relat_1(sK12(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_204])])).

fof(f3769,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK24))))
    | ~ spl28_204 ),
    inference(resolution,[],[f1370,f340])).

fof(f1370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK24)))
        | v1_relat_1(X0) )
    | ~ spl28_204 ),
    inference(resolution,[],[f1368,f287])).

fof(f1368,plain,
    ( v1_relat_1(sK12(sK24))
    | ~ spl28_204 ),
    inference(avatar_component_clause,[],[f1367])).

fof(f3779,plain,
    ( spl28_536
    | ~ spl28_204 ),
    inference(avatar_split_clause,[],[f3771,f1367,f3777])).

fof(f3777,plain,
    ( spl28_536
  <=> v1_relat_1(sK12(sK12(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_536])])).

fof(f3771,plain,
    ( v1_relat_1(sK12(sK12(sK24)))
    | ~ spl28_204 ),
    inference(resolution,[],[f1370,f343])).

fof(f3756,plain,
    ( spl28_534
    | ~ spl28_64
    | ~ spl28_66
    | spl28_187 ),
    inference(avatar_split_clause,[],[f3605,f1272,f634,f627,f3754])).

fof(f3754,plain,
    ( spl28_534
  <=> v1_funct_1(k6_domain_1(sK27,sK10(sK27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_534])])).

fof(f627,plain,
    ( spl28_64
  <=> v1_relat_1(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_64])])).

fof(f634,plain,
    ( spl28_66
  <=> v1_funct_1(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_66])])).

fof(f1272,plain,
    ( spl28_187
  <=> ~ v1_xboole_0(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_187])])).

fof(f3605,plain,
    ( v1_funct_1(k6_domain_1(sK27,sK10(sK27)))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f3578,f1273])).

fof(f1273,plain,
    ( ~ v1_xboole_0(sK27)
    | ~ spl28_187 ),
    inference(avatar_component_clause,[],[f1272])).

fof(f3578,plain,
    ( v1_xboole_0(sK27)
    | v1_funct_1(k6_domain_1(sK27,sK10(sK27)))
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f2382,f1858])).

fof(f1858,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK27))
        | v1_funct_1(X8) )
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(subsumption_resolution,[],[f1850,f628])).

fof(f628,plain,
    ( v1_relat_1(sK27)
    | ~ spl28_64 ),
    inference(avatar_component_clause,[],[f627])).

fof(f1850,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK27))
        | v1_funct_1(X8)
        | ~ v1_relat_1(sK27) )
    | ~ spl28_66 ),
    inference(resolution,[],[f329,f635])).

fof(f635,plain,
    ( v1_funct_1(sK27)
    | ~ spl28_66 ),
    inference(avatar_component_clause,[],[f634])).

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_funct_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f172])).

fof(f172,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc3_funct_1)).

fof(f2382,plain,(
    ! [X9] :
      ( m1_subset_1(k6_domain_1(X9,sK10(X9)),k1_zfmisc_1(X9))
      | v1_xboole_0(X9) ) ),
    inference(resolution,[],[f349,f340])).

fof(f3745,plain,
    ( spl28_532
    | ~ spl28_58
    | ~ spl28_60
    | spl28_73 ),
    inference(avatar_split_clause,[],[f3603,f657,f613,f606,f3743])).

fof(f3743,plain,
    ( spl28_532
  <=> v1_funct_1(k6_domain_1(sK26,sK10(sK26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_532])])).

fof(f606,plain,
    ( spl28_58
  <=> v1_relat_1(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_58])])).

fof(f613,plain,
    ( spl28_60
  <=> v1_funct_1(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_60])])).

fof(f657,plain,
    ( spl28_73
  <=> ~ v1_xboole_0(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_73])])).

fof(f3603,plain,
    ( v1_funct_1(k6_domain_1(sK26,sK10(sK26)))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f3576,f658])).

fof(f658,plain,
    ( ~ v1_xboole_0(sK26)
    | ~ spl28_73 ),
    inference(avatar_component_clause,[],[f657])).

fof(f3576,plain,
    ( v1_xboole_0(sK26)
    | v1_funct_1(k6_domain_1(sK26,sK10(sK26)))
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f2382,f1857])).

fof(f1857,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(sK26))
        | v1_funct_1(X7) )
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(subsumption_resolution,[],[f1849,f607])).

fof(f607,plain,
    ( v1_relat_1(sK26)
    | ~ spl28_58 ),
    inference(avatar_component_clause,[],[f606])).

fof(f1849,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(sK26))
        | v1_funct_1(X7)
        | ~ v1_relat_1(sK26) )
    | ~ spl28_60 ),
    inference(resolution,[],[f329,f614])).

fof(f614,plain,
    ( v1_funct_1(sK26)
    | ~ spl28_60 ),
    inference(avatar_component_clause,[],[f613])).

fof(f3733,plain,
    ( spl28_530
    | ~ spl28_54
    | ~ spl28_56
    | spl28_181 ),
    inference(avatar_split_clause,[],[f3600,f1251,f599,f592,f3731])).

fof(f3731,plain,
    ( spl28_530
  <=> v1_funct_1(k6_domain_1(sK25,sK10(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_530])])).

fof(f592,plain,
    ( spl28_54
  <=> v1_relat_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_54])])).

fof(f599,plain,
    ( spl28_56
  <=> v1_funct_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_56])])).

fof(f1251,plain,
    ( spl28_181
  <=> ~ v1_xboole_0(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_181])])).

fof(f3600,plain,
    ( v1_funct_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_54
    | ~ spl28_56
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f3573,f1252])).

fof(f1252,plain,
    ( ~ v1_xboole_0(sK25)
    | ~ spl28_181 ),
    inference(avatar_component_clause,[],[f1251])).

fof(f3573,plain,
    ( v1_xboole_0(sK25)
    | v1_funct_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f2382,f1856])).

fof(f1856,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK25))
        | v1_funct_1(X6) )
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(subsumption_resolution,[],[f1848,f593])).

fof(f593,plain,
    ( v1_relat_1(sK25)
    | ~ spl28_54 ),
    inference(avatar_component_clause,[],[f592])).

fof(f1848,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK25))
        | v1_funct_1(X6)
        | ~ v1_relat_1(sK25) )
    | ~ spl28_56 ),
    inference(resolution,[],[f329,f600])).

fof(f600,plain,
    ( v1_funct_1(sK25)
    | ~ spl28_56 ),
    inference(avatar_component_clause,[],[f599])).

fof(f3722,plain,
    ( spl28_528
    | ~ spl28_50
    | ~ spl28_52
    | spl28_175 ),
    inference(avatar_split_clause,[],[f3598,f1230,f585,f578,f3720])).

fof(f3720,plain,
    ( spl28_528
  <=> v1_funct_1(k6_domain_1(sK24,sK10(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_528])])).

fof(f578,plain,
    ( spl28_50
  <=> v1_relat_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_50])])).

fof(f585,plain,
    ( spl28_52
  <=> v1_funct_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_52])])).

fof(f1230,plain,
    ( spl28_175
  <=> ~ v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_175])])).

fof(f3598,plain,
    ( v1_funct_1(k6_domain_1(sK24,sK10(sK24)))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f3571,f1231])).

fof(f1231,plain,
    ( ~ v1_xboole_0(sK24)
    | ~ spl28_175 ),
    inference(avatar_component_clause,[],[f1230])).

fof(f3571,plain,
    ( v1_xboole_0(sK24)
    | v1_funct_1(k6_domain_1(sK24,sK10(sK24)))
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f2382,f1855])).

fof(f1855,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK24))
        | v1_funct_1(X5) )
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(subsumption_resolution,[],[f1847,f579])).

fof(f579,plain,
    ( v1_relat_1(sK24)
    | ~ spl28_50 ),
    inference(avatar_component_clause,[],[f578])).

fof(f1847,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK24))
        | v1_funct_1(X5)
        | ~ v1_relat_1(sK24) )
    | ~ spl28_52 ),
    inference(resolution,[],[f329,f586])).

fof(f586,plain,
    ( v1_funct_1(sK24)
    | ~ spl28_52 ),
    inference(avatar_component_clause,[],[f585])).

fof(f3711,plain,
    ( spl28_526
    | spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f3594,f508,f501,f494,f3709])).

fof(f3709,plain,
    ( spl28_526
  <=> v1_funct_1(k6_domain_1(sK19,sK10(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_526])])).

fof(f494,plain,
    ( spl28_27
  <=> ~ v1_xboole_0(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_27])])).

fof(f501,plain,
    ( spl28_28
  <=> v1_relat_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_28])])).

fof(f508,plain,
    ( spl28_30
  <=> v1_funct_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_30])])).

fof(f3594,plain,
    ( v1_funct_1(k6_domain_1(sK19,sK10(sK19)))
    | ~ spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f3567,f495])).

fof(f495,plain,
    ( ~ v1_xboole_0(sK19)
    | ~ spl28_27 ),
    inference(avatar_component_clause,[],[f494])).

fof(f3567,plain,
    ( v1_xboole_0(sK19)
    | v1_funct_1(k6_domain_1(sK19,sK10(sK19)))
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f2382,f1854])).

fof(f1854,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK19))
        | v1_funct_1(X4) )
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f1846,f502])).

fof(f502,plain,
    ( v1_relat_1(sK19)
    | ~ spl28_28 ),
    inference(avatar_component_clause,[],[f501])).

fof(f1846,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK19))
        | v1_funct_1(X4)
        | ~ v1_relat_1(sK19) )
    | ~ spl28_30 ),
    inference(resolution,[],[f329,f509])).

fof(f509,plain,
    ( v1_funct_1(sK19)
    | ~ spl28_30 ),
    inference(avatar_component_clause,[],[f508])).

fof(f3701,plain,
    ( spl28_524
    | spl28_23
    | ~ spl28_120 ),
    inference(avatar_split_clause,[],[f3592,f948,f480,f3699])).

fof(f3699,plain,
    ( spl28_524
  <=> v1_zfmisc_1(k6_domain_1(sK18,sK10(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_524])])).

fof(f480,plain,
    ( spl28_23
  <=> ~ v1_xboole_0(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_23])])).

fof(f948,plain,
    ( spl28_120
  <=> v1_zfmisc_1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_120])])).

fof(f3592,plain,
    ( v1_zfmisc_1(k6_domain_1(sK18,sK10(sK18)))
    | ~ spl28_23
    | ~ spl28_120 ),
    inference(subsumption_resolution,[],[f3565,f481])).

fof(f481,plain,
    ( ~ v1_xboole_0(sK18)
    | ~ spl28_23 ),
    inference(avatar_component_clause,[],[f480])).

fof(f3565,plain,
    ( v1_xboole_0(sK18)
    | v1_zfmisc_1(k6_domain_1(sK18,sK10(sK18)))
    | ~ spl28_120 ),
    inference(resolution,[],[f2382,f957])).

fof(f957,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK18))
        | v1_zfmisc_1(X0) )
    | ~ spl28_120 ),
    inference(resolution,[],[f949,f289])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_zfmisc_1(X1) ) ),
    inference(cnf_transformation,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_zfmisc_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0) ) ),
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_zfmisc_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc5_funct_1)).

fof(f949,plain,
    ( v1_zfmisc_1(sK18)
    | ~ spl28_120 ),
    inference(avatar_component_clause,[],[f948])).

fof(f3693,plain,
    ( spl28_522
    | spl28_19
    | ~ spl28_100 ),
    inference(avatar_split_clause,[],[f3590,f845,f466,f3691])).

fof(f3691,plain,
    ( spl28_522
  <=> v1_zfmisc_1(k6_domain_1(sK17,sK10(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_522])])).

fof(f466,plain,
    ( spl28_19
  <=> ~ v1_xboole_0(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_19])])).

fof(f845,plain,
    ( spl28_100
  <=> v1_zfmisc_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_100])])).

fof(f3590,plain,
    ( v1_zfmisc_1(k6_domain_1(sK17,sK10(sK17)))
    | ~ spl28_19
    | ~ spl28_100 ),
    inference(subsumption_resolution,[],[f3563,f467])).

fof(f467,plain,
    ( ~ v1_xboole_0(sK17)
    | ~ spl28_19 ),
    inference(avatar_component_clause,[],[f466])).

fof(f3563,plain,
    ( v1_xboole_0(sK17)
    | v1_zfmisc_1(k6_domain_1(sK17,sK10(sK17)))
    | ~ spl28_100 ),
    inference(resolution,[],[f2382,f909])).

fof(f909,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,k1_zfmisc_1(sK17))
        | v1_zfmisc_1(X14) )
    | ~ spl28_100 ),
    inference(resolution,[],[f289,f846])).

fof(f846,plain,
    ( v1_zfmisc_1(sK17)
    | ~ spl28_100 ),
    inference(avatar_component_clause,[],[f845])).

fof(f3685,plain,
    ( spl28_520
    | ~ spl28_176
    | spl28_181 ),
    inference(avatar_split_clause,[],[f3601,f1251,f1234,f3683])).

fof(f3683,plain,
    ( spl28_520
  <=> v1_zfmisc_1(k6_domain_1(sK25,sK10(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_520])])).

fof(f1234,plain,
    ( spl28_176
  <=> v1_zfmisc_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_176])])).

fof(f3601,plain,
    ( v1_zfmisc_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_176
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f3574,f1252])).

fof(f3574,plain,
    ( v1_xboole_0(sK25)
    | v1_zfmisc_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_176 ),
    inference(resolution,[],[f2382,f1556])).

fof(f1556,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK25))
        | v1_zfmisc_1(X0) )
    | ~ spl28_176 ),
    inference(resolution,[],[f1235,f289])).

fof(f1235,plain,
    ( v1_zfmisc_1(sK25)
    | ~ spl28_176 ),
    inference(avatar_component_clause,[],[f1234])).

fof(f3677,plain,
    ( spl28_518
    | ~ spl28_64
    | spl28_187 ),
    inference(avatar_split_clause,[],[f3606,f1272,f627,f3675])).

fof(f3675,plain,
    ( spl28_518
  <=> v1_relat_1(k6_domain_1(sK27,sK10(sK27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_518])])).

fof(f3606,plain,
    ( v1_relat_1(k6_domain_1(sK27,sK10(sK27)))
    | ~ spl28_64
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f3579,f1273])).

fof(f3579,plain,
    ( v1_xboole_0(sK27)
    | v1_relat_1(k6_domain_1(sK27,sK10(sK27)))
    | ~ spl28_64 ),
    inference(resolution,[],[f2382,f770])).

fof(f770,plain,
    ( ! [X10] :
        ( ~ m1_subset_1(X10,k1_zfmisc_1(sK27))
        | v1_relat_1(X10) )
    | ~ spl28_64 ),
    inference(resolution,[],[f287,f628])).

fof(f3669,plain,
    ( spl28_516
    | ~ spl28_58
    | spl28_73 ),
    inference(avatar_split_clause,[],[f3604,f657,f606,f3667])).

fof(f3667,plain,
    ( spl28_516
  <=> v1_relat_1(k6_domain_1(sK26,sK10(sK26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_516])])).

fof(f3604,plain,
    ( v1_relat_1(k6_domain_1(sK26,sK10(sK26)))
    | ~ spl28_58
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f3577,f658])).

fof(f3577,plain,
    ( v1_xboole_0(sK26)
    | v1_relat_1(k6_domain_1(sK26,sK10(sK26)))
    | ~ spl28_58 ),
    inference(resolution,[],[f2382,f769])).

fof(f769,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,k1_zfmisc_1(sK26))
        | v1_relat_1(X9) )
    | ~ spl28_58 ),
    inference(resolution,[],[f287,f607])).

fof(f3661,plain,
    ( spl28_514
    | ~ spl28_54
    | spl28_181 ),
    inference(avatar_split_clause,[],[f3602,f1251,f592,f3659])).

fof(f3659,plain,
    ( spl28_514
  <=> v1_relat_1(k6_domain_1(sK25,sK10(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_514])])).

fof(f3602,plain,
    ( v1_relat_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_54
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f3575,f1252])).

fof(f3575,plain,
    ( v1_xboole_0(sK25)
    | v1_relat_1(k6_domain_1(sK25,sK10(sK25)))
    | ~ spl28_54 ),
    inference(resolution,[],[f2382,f768])).

fof(f768,plain,
    ( ! [X8] :
        ( ~ m1_subset_1(X8,k1_zfmisc_1(sK25))
        | v1_relat_1(X8) )
    | ~ spl28_54 ),
    inference(resolution,[],[f287,f593])).

fof(f3653,plain,
    ( spl28_512
    | ~ spl28_50
    | spl28_175 ),
    inference(avatar_split_clause,[],[f3599,f1230,f578,f3651])).

fof(f3651,plain,
    ( spl28_512
  <=> v1_relat_1(k6_domain_1(sK24,sK10(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_512])])).

fof(f3599,plain,
    ( v1_relat_1(k6_domain_1(sK24,sK10(sK24)))
    | ~ spl28_50
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f3572,f1231])).

fof(f3572,plain,
    ( v1_xboole_0(sK24)
    | v1_relat_1(k6_domain_1(sK24,sK10(sK24)))
    | ~ spl28_50 ),
    inference(resolution,[],[f2382,f767])).

fof(f767,plain,
    ( ! [X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(sK24))
        | v1_relat_1(X7) )
    | ~ spl28_50 ),
    inference(resolution,[],[f287,f579])).

fof(f3645,plain,
    ( spl28_510
    | spl28_33
    | ~ spl28_34 ),
    inference(avatar_split_clause,[],[f3596,f522,f515,f3643])).

fof(f3643,plain,
    ( spl28_510
  <=> v1_zfmisc_1(k6_domain_1(sK20,sK10(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_510])])).

fof(f515,plain,
    ( spl28_33
  <=> ~ v1_xboole_0(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_33])])).

fof(f522,plain,
    ( spl28_34
  <=> v1_zfmisc_1(sK20) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_34])])).

fof(f3596,plain,
    ( v1_zfmisc_1(k6_domain_1(sK20,sK10(sK20)))
    | ~ spl28_33
    | ~ spl28_34 ),
    inference(subsumption_resolution,[],[f3569,f516])).

fof(f516,plain,
    ( ~ v1_xboole_0(sK20)
    | ~ spl28_33 ),
    inference(avatar_component_clause,[],[f515])).

fof(f3569,plain,
    ( v1_xboole_0(sK20)
    | v1_zfmisc_1(k6_domain_1(sK20,sK10(sK20)))
    | ~ spl28_34 ),
    inference(resolution,[],[f2382,f910])).

fof(f910,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(sK20))
        | v1_zfmisc_1(X15) )
    | ~ spl28_34 ),
    inference(resolution,[],[f289,f523])).

fof(f523,plain,
    ( v1_zfmisc_1(sK20)
    | ~ spl28_34 ),
    inference(avatar_component_clause,[],[f522])).

fof(f3637,plain,
    ( spl28_508
    | spl28_27
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f3595,f501,f494,f3635])).

fof(f3635,plain,
    ( spl28_508
  <=> v1_relat_1(k6_domain_1(sK19,sK10(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_508])])).

fof(f3595,plain,
    ( v1_relat_1(k6_domain_1(sK19,sK10(sK19)))
    | ~ spl28_27
    | ~ spl28_28 ),
    inference(subsumption_resolution,[],[f3568,f495])).

fof(f3568,plain,
    ( v1_xboole_0(sK19)
    | v1_relat_1(k6_domain_1(sK19,sK10(sK19)))
    | ~ spl28_28 ),
    inference(resolution,[],[f2382,f765])).

fof(f765,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(sK19))
        | v1_relat_1(X5) )
    | ~ spl28_28 ),
    inference(resolution,[],[f287,f502])).

fof(f3629,plain,
    ( spl28_506
    | spl28_23
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f3593,f487,f480,f3627])).

fof(f3627,plain,
    ( spl28_506
  <=> v1_relat_1(k6_domain_1(sK18,sK10(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_506])])).

fof(f487,plain,
    ( spl28_24
  <=> v1_relat_1(sK18) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_24])])).

fof(f3593,plain,
    ( v1_relat_1(k6_domain_1(sK18,sK10(sK18)))
    | ~ spl28_23
    | ~ spl28_24 ),
    inference(subsumption_resolution,[],[f3566,f481])).

fof(f3566,plain,
    ( v1_xboole_0(sK18)
    | v1_relat_1(k6_domain_1(sK18,sK10(sK18)))
    | ~ spl28_24 ),
    inference(resolution,[],[f2382,f764])).

fof(f764,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(sK18))
        | v1_relat_1(X4) )
    | ~ spl28_24 ),
    inference(resolution,[],[f287,f488])).

fof(f488,plain,
    ( v1_relat_1(sK18)
    | ~ spl28_24 ),
    inference(avatar_component_clause,[],[f487])).

fof(f3619,plain,
    ( spl28_504
    | spl28_19
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f3591,f473,f466,f3617])).

fof(f3617,plain,
    ( spl28_504
  <=> v4_funct_1(k6_domain_1(sK17,sK10(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_504])])).

fof(f473,plain,
    ( spl28_20
  <=> v4_funct_1(sK17) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_20])])).

fof(f3591,plain,
    ( v4_funct_1(k6_domain_1(sK17,sK10(sK17)))
    | ~ spl28_19
    | ~ spl28_20 ),
    inference(subsumption_resolution,[],[f3564,f467])).

fof(f3564,plain,
    ( v1_xboole_0(sK17)
    | v4_funct_1(k6_domain_1(sK17,sK10(sK17)))
    | ~ spl28_20 ),
    inference(resolution,[],[f2382,f743])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK17))
        | v4_funct_1(X0) )
    | ~ spl28_20 ),
    inference(resolution,[],[f278,f474])).

fof(f474,plain,
    ( v4_funct_1(sK17)
    | ~ spl28_20 ),
    inference(avatar_component_clause,[],[f473])).

fof(f278,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v4_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v4_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc10_funct_1)).

fof(f3532,plain,
    ( spl28_502
    | ~ spl28_152 ),
    inference(avatar_split_clause,[],[f3514,f1111,f3530])).

fof(f3530,plain,
    ( spl28_502
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK9(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_502])])).

fof(f1111,plain,
    ( spl28_152
  <=> v1_relat_1(sK9(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_152])])).

fof(f3514,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK9(sK19))))
    | ~ spl28_152 ),
    inference(resolution,[],[f1203,f340])).

fof(f1203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK9(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_152 ),
    inference(resolution,[],[f1112,f287])).

fof(f1112,plain,
    ( v1_relat_1(sK9(sK19))
    | ~ spl28_152 ),
    inference(avatar_component_clause,[],[f1111])).

fof(f3524,plain,
    ( spl28_500
    | ~ spl28_152 ),
    inference(avatar_split_clause,[],[f3516,f1111,f3522])).

fof(f3522,plain,
    ( spl28_500
  <=> v1_relat_1(sK12(sK9(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_500])])).

fof(f3516,plain,
    ( v1_relat_1(sK12(sK9(sK19)))
    | ~ spl28_152 ),
    inference(resolution,[],[f1203,f343])).

fof(f3505,plain,
    ( spl28_498
    | ~ spl28_150 ),
    inference(avatar_split_clause,[],[f3487,f1103,f3503])).

fof(f3503,plain,
    ( spl28_498
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK8(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_498])])).

fof(f1103,plain,
    ( spl28_150
  <=> v1_relat_1(sK8(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_150])])).

fof(f3487,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK8(sK19))))
    | ~ spl28_150 ),
    inference(resolution,[],[f1202,f340])).

fof(f1202,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK8(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_150 ),
    inference(resolution,[],[f1104,f287])).

fof(f1104,plain,
    ( v1_relat_1(sK8(sK19))
    | ~ spl28_150 ),
    inference(avatar_component_clause,[],[f1103])).

fof(f3497,plain,
    ( spl28_496
    | ~ spl28_150 ),
    inference(avatar_split_clause,[],[f3489,f1103,f3495])).

fof(f3495,plain,
    ( spl28_496
  <=> v1_relat_1(sK12(sK8(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_496])])).

fof(f3489,plain,
    ( v1_relat_1(sK12(sK8(sK19)))
    | ~ spl28_150 ),
    inference(resolution,[],[f1202,f343])).

fof(f3479,plain,
    ( ~ spl28_495
    | spl28_491 ),
    inference(avatar_split_clause,[],[f3472,f3463,f3477])).

fof(f3477,plain,
    ( spl28_495
  <=> ~ v1_xboole_0(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_495])])).

fof(f3463,plain,
    ( spl28_491
  <=> ~ v1_zfmisc_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_491])])).

fof(f3472,plain,
    ( ~ v1_xboole_0(sK10(sK17))
    | ~ spl28_491 ),
    inference(resolution,[],[f3464,f263])).

fof(f3464,plain,
    ( ~ v1_zfmisc_1(sK10(sK17))
    | ~ spl28_491 ),
    inference(avatar_component_clause,[],[f3463])).

fof(f3471,plain,
    ( ~ spl28_491
    | spl28_492
    | ~ spl28_78
    | ~ spl28_80 ),
    inference(avatar_split_clause,[],[f1176,f698,f688,f3469,f3463])).

fof(f3469,plain,
    ( spl28_492
  <=> v3_funct_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_492])])).

fof(f688,plain,
    ( spl28_78
  <=> v1_relat_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_78])])).

fof(f698,plain,
    ( spl28_80
  <=> v1_funct_1(sK10(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_80])])).

fof(f1176,plain,
    ( v3_funct_1(sK10(sK17))
    | ~ v1_zfmisc_1(sK10(sK17))
    | ~ spl28_78
    | ~ spl28_80 ),
    inference(subsumption_resolution,[],[f1169,f689])).

fof(f689,plain,
    ( v1_relat_1(sK10(sK17))
    | ~ spl28_78 ),
    inference(avatar_component_clause,[],[f688])).

fof(f1169,plain,
    ( v3_funct_1(sK10(sK17))
    | ~ v1_zfmisc_1(sK10(sK17))
    | ~ v1_relat_1(sK10(sK17))
    | ~ spl28_80 ),
    inference(resolution,[],[f325,f699])).

fof(f699,plain,
    ( v1_funct_1(sK10(sK17))
    | ~ spl28_80 ),
    inference(avatar_component_clause,[],[f698])).

fof(f325,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | v3_funct_1(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f168])).

fof(f168,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) )
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f167])).

fof(f167,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) )
      | v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_zfmisc_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc6_funct_1)).

fof(f3388,plain,
    ( spl28_488
    | ~ spl28_136 ),
    inference(avatar_split_clause,[],[f3370,f1023,f3386])).

fof(f3386,plain,
    ( spl28_488
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_488])])).

fof(f1023,plain,
    ( spl28_136
  <=> v1_relat_1(sK5(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_136])])).

fof(f3370,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK19))))
    | ~ spl28_136 ),
    inference(resolution,[],[f1026,f340])).

fof(f1026,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_136 ),
    inference(resolution,[],[f1024,f287])).

fof(f1024,plain,
    ( v1_relat_1(sK5(sK19))
    | ~ spl28_136 ),
    inference(avatar_component_clause,[],[f1023])).

fof(f3380,plain,
    ( spl28_486
    | ~ spl28_136 ),
    inference(avatar_split_clause,[],[f3372,f1023,f3378])).

fof(f3378,plain,
    ( spl28_486
  <=> v1_relat_1(sK12(sK5(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_486])])).

fof(f3372,plain,
    ( v1_relat_1(sK12(sK5(sK19)))
    | ~ spl28_136 ),
    inference(resolution,[],[f1026,f343])).

fof(f3360,plain,
    ( spl28_484
    | ~ spl28_134 ),
    inference(avatar_split_clause,[],[f3342,f1015,f3358])).

fof(f3358,plain,
    ( spl28_484
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_484])])).

fof(f1015,plain,
    ( spl28_134
  <=> v1_relat_1(sK4(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_134])])).

fof(f3342,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK19))))
    | ~ spl28_134 ),
    inference(resolution,[],[f1018,f340])).

fof(f1018,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_134 ),
    inference(resolution,[],[f1016,f287])).

fof(f1016,plain,
    ( v1_relat_1(sK4(sK19))
    | ~ spl28_134 ),
    inference(avatar_component_clause,[],[f1015])).

fof(f3352,plain,
    ( spl28_482
    | ~ spl28_134 ),
    inference(avatar_split_clause,[],[f3344,f1015,f3350])).

fof(f3350,plain,
    ( spl28_482
  <=> v1_relat_1(sK12(sK4(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_482])])).

fof(f3344,plain,
    ( v1_relat_1(sK12(sK4(sK19)))
    | ~ spl28_134 ),
    inference(resolution,[],[f1018,f343])).

fof(f3333,plain,
    ( spl28_480
    | ~ spl28_132 ),
    inference(avatar_split_clause,[],[f3315,f1007,f3331])).

fof(f3331,plain,
    ( spl28_480
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_480])])).

fof(f1007,plain,
    ( spl28_132
  <=> v1_relat_1(sK3(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_132])])).

fof(f3315,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK19))))
    | ~ spl28_132 ),
    inference(resolution,[],[f1010,f340])).

fof(f1010,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_132 ),
    inference(resolution,[],[f1008,f287])).

fof(f1008,plain,
    ( v1_relat_1(sK3(sK19))
    | ~ spl28_132 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f3325,plain,
    ( spl28_478
    | ~ spl28_132 ),
    inference(avatar_split_clause,[],[f3317,f1007,f3323])).

fof(f3323,plain,
    ( spl28_478
  <=> v1_relat_1(sK12(sK3(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_478])])).

fof(f3317,plain,
    ( v1_relat_1(sK12(sK3(sK19)))
    | ~ spl28_132 ),
    inference(resolution,[],[f1010,f343])).

fof(f3306,plain,
    ( spl28_476
    | ~ spl28_130 ),
    inference(avatar_split_clause,[],[f3288,f999,f3304])).

fof(f3304,plain,
    ( spl28_476
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK2(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_476])])).

fof(f999,plain,
    ( spl28_130
  <=> v1_relat_1(sK2(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_130])])).

fof(f3288,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK2(sK19))))
    | ~ spl28_130 ),
    inference(resolution,[],[f1002,f340])).

fof(f1002,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_130 ),
    inference(resolution,[],[f1000,f287])).

fof(f1000,plain,
    ( v1_relat_1(sK2(sK19))
    | ~ spl28_130 ),
    inference(avatar_component_clause,[],[f999])).

fof(f3298,plain,
    ( spl28_474
    | ~ spl28_130 ),
    inference(avatar_split_clause,[],[f3290,f999,f3296])).

fof(f3296,plain,
    ( spl28_474
  <=> v1_relat_1(sK12(sK2(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_474])])).

fof(f3290,plain,
    ( v1_relat_1(sK12(sK2(sK19)))
    | ~ spl28_130 ),
    inference(resolution,[],[f1002,f343])).

fof(f3279,plain,
    ( spl28_472
    | ~ spl28_126 ),
    inference(avatar_split_clause,[],[f3261,f984,f3277])).

fof(f3277,plain,
    ( spl28_472
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK19)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_472])])).

fof(f984,plain,
    ( spl28_126
  <=> v1_relat_1(sK12(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_126])])).

fof(f3261,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK19))))
    | ~ spl28_126 ),
    inference(resolution,[],[f987,f340])).

fof(f987,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK19)))
        | v1_relat_1(X0) )
    | ~ spl28_126 ),
    inference(resolution,[],[f985,f287])).

fof(f985,plain,
    ( v1_relat_1(sK12(sK19))
    | ~ spl28_126 ),
    inference(avatar_component_clause,[],[f984])).

fof(f3271,plain,
    ( spl28_470
    | ~ spl28_126 ),
    inference(avatar_split_clause,[],[f3263,f984,f3269])).

fof(f3269,plain,
    ( spl28_470
  <=> v1_relat_1(sK12(sK12(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_470])])).

fof(f3263,plain,
    ( v1_relat_1(sK12(sK12(sK19)))
    | ~ spl28_126 ),
    inference(resolution,[],[f987,f343])).

fof(f3232,plain,
    ( spl28_468
    | ~ spl28_118 ),
    inference(avatar_split_clause,[],[f3214,f939,f3230])).

fof(f3230,plain,
    ( spl28_468
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK5(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_468])])).

fof(f939,plain,
    ( spl28_118
  <=> v1_relat_1(sK5(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_118])])).

fof(f3214,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK5(sK18))))
    | ~ spl28_118 ),
    inference(resolution,[],[f942,f340])).

fof(f942,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK18)))
        | v1_relat_1(X0) )
    | ~ spl28_118 ),
    inference(resolution,[],[f940,f287])).

fof(f940,plain,
    ( v1_relat_1(sK5(sK18))
    | ~ spl28_118 ),
    inference(avatar_component_clause,[],[f939])).

fof(f3224,plain,
    ( spl28_466
    | ~ spl28_118 ),
    inference(avatar_split_clause,[],[f3216,f939,f3222])).

fof(f3222,plain,
    ( spl28_466
  <=> v1_relat_1(sK12(sK5(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_466])])).

fof(f3216,plain,
    ( v1_relat_1(sK12(sK5(sK18)))
    | ~ spl28_118 ),
    inference(resolution,[],[f942,f343])).

fof(f3205,plain,
    ( spl28_464
    | ~ spl28_116 ),
    inference(avatar_split_clause,[],[f3187,f931,f3203])).

fof(f3203,plain,
    ( spl28_464
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK4(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_464])])).

fof(f931,plain,
    ( spl28_116
  <=> v1_relat_1(sK4(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_116])])).

fof(f3187,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK4(sK18))))
    | ~ spl28_116 ),
    inference(resolution,[],[f934,f340])).

fof(f934,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK18)))
        | v1_relat_1(X0) )
    | ~ spl28_116 ),
    inference(resolution,[],[f932,f287])).

fof(f932,plain,
    ( v1_relat_1(sK4(sK18))
    | ~ spl28_116 ),
    inference(avatar_component_clause,[],[f931])).

fof(f3197,plain,
    ( spl28_462
    | ~ spl28_116 ),
    inference(avatar_split_clause,[],[f3189,f931,f3195])).

fof(f3195,plain,
    ( spl28_462
  <=> v1_relat_1(sK12(sK4(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_462])])).

fof(f3189,plain,
    ( v1_relat_1(sK12(sK4(sK18)))
    | ~ spl28_116 ),
    inference(resolution,[],[f934,f343])).

fof(f3178,plain,
    ( spl28_460
    | ~ spl28_114 ),
    inference(avatar_split_clause,[],[f3160,f923,f3176])).

fof(f3176,plain,
    ( spl28_460
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK3(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_460])])).

fof(f923,plain,
    ( spl28_114
  <=> v1_relat_1(sK3(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_114])])).

fof(f3160,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK3(sK18))))
    | ~ spl28_114 ),
    inference(resolution,[],[f926,f340])).

fof(f926,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK18)))
        | v1_relat_1(X0) )
    | ~ spl28_114 ),
    inference(resolution,[],[f924,f287])).

fof(f924,plain,
    ( v1_relat_1(sK3(sK18))
    | ~ spl28_114 ),
    inference(avatar_component_clause,[],[f923])).

fof(f3170,plain,
    ( spl28_458
    | ~ spl28_114 ),
    inference(avatar_split_clause,[],[f3162,f923,f3168])).

fof(f3168,plain,
    ( spl28_458
  <=> v1_relat_1(sK12(sK3(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_458])])).

fof(f3162,plain,
    ( v1_relat_1(sK12(sK3(sK18)))
    | ~ spl28_114 ),
    inference(resolution,[],[f926,f343])).

fof(f3151,plain,
    ( spl28_456
    | ~ spl28_112 ),
    inference(avatar_split_clause,[],[f3133,f915,f3149])).

fof(f3149,plain,
    ( spl28_456
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK2(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_456])])).

fof(f915,plain,
    ( spl28_112
  <=> v1_relat_1(sK2(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_112])])).

fof(f3133,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK2(sK18))))
    | ~ spl28_112 ),
    inference(resolution,[],[f918,f340])).

fof(f918,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK18)))
        | v1_relat_1(X0) )
    | ~ spl28_112 ),
    inference(resolution,[],[f916,f287])).

fof(f916,plain,
    ( v1_relat_1(sK2(sK18))
    | ~ spl28_112 ),
    inference(avatar_component_clause,[],[f915])).

fof(f3143,plain,
    ( spl28_454
    | ~ spl28_112 ),
    inference(avatar_split_clause,[],[f3135,f915,f3141])).

fof(f3141,plain,
    ( spl28_454
  <=> v1_relat_1(sK12(sK2(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_454])])).

fof(f3135,plain,
    ( v1_relat_1(sK12(sK2(sK18)))
    | ~ spl28_112 ),
    inference(resolution,[],[f918,f343])).

fof(f3106,plain,
    ( spl28_452
    | ~ spl28_108 ),
    inference(avatar_split_clause,[],[f3088,f891,f3104])).

fof(f3104,plain,
    ( spl28_452
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK12(sK18)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_452])])).

fof(f891,plain,
    ( spl28_108
  <=> v1_relat_1(sK12(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_108])])).

fof(f3088,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK12(sK18))))
    | ~ spl28_108 ),
    inference(resolution,[],[f894,f340])).

fof(f894,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK18)))
        | v1_relat_1(X0) )
    | ~ spl28_108 ),
    inference(resolution,[],[f892,f287])).

fof(f892,plain,
    ( v1_relat_1(sK12(sK18))
    | ~ spl28_108 ),
    inference(avatar_component_clause,[],[f891])).

fof(f3098,plain,
    ( spl28_450
    | ~ spl28_108 ),
    inference(avatar_split_clause,[],[f3090,f891,f3096])).

fof(f3096,plain,
    ( spl28_450
  <=> v1_relat_1(sK12(sK12(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_450])])).

fof(f3090,plain,
    ( v1_relat_1(sK12(sK12(sK18)))
    | ~ spl28_108 ),
    inference(resolution,[],[f894,f343])).

fof(f3079,plain,
    ( spl28_448
    | ~ spl28_90 ),
    inference(avatar_split_clause,[],[f3072,f795,f3077])).

fof(f3077,plain,
    ( spl28_448
  <=> v1_relat_1(sK10(sK10(k1_zfmisc_1(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_448])])).

fof(f795,plain,
    ( spl28_90
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_90])])).

fof(f3072,plain,
    ( v1_relat_1(sK10(sK10(k1_zfmisc_1(sK17))))
    | ~ spl28_90 ),
    inference(resolution,[],[f840,f340])).

fof(f840,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK10(k1_zfmisc_1(sK17)))
        | v1_relat_1(X2) )
    | ~ spl28_90 ),
    inference(resolution,[],[f796,f276])).

fof(f276,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
          | ~ m1_subset_1(X1,X0) )
      | ~ v4_funct_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v4_funct_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => ( v1_funct_1(X1)
            & v1_relat_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc9_funct_1)).

fof(f796,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl28_90 ),
    inference(avatar_component_clause,[],[f795])).

fof(f3069,plain,
    ( spl28_446
    | ~ spl28_90 ),
    inference(avatar_split_clause,[],[f3062,f795,f3067])).

fof(f3067,plain,
    ( spl28_446
  <=> v1_funct_1(sK10(sK10(k1_zfmisc_1(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_446])])).

fof(f3062,plain,
    ( v1_funct_1(sK10(sK10(k1_zfmisc_1(sK17))))
    | ~ spl28_90 ),
    inference(resolution,[],[f839,f340])).

fof(f839,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK10(k1_zfmisc_1(sK17)))
        | v1_funct_1(X1) )
    | ~ spl28_90 ),
    inference(resolution,[],[f796,f277])).

fof(f277,plain,(
    ! [X0,X1] :
      ( ~ v4_funct_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f112])).

fof(f3058,plain,
    ( spl28_444
    | ~ spl28_98 ),
    inference(avatar_split_clause,[],[f3038,f832,f3056])).

fof(f3056,plain,
    ( spl28_444
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK5(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_444])])).

fof(f832,plain,
    ( spl28_98
  <=> v4_funct_1(sK5(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_98])])).

fof(f3038,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK5(sK17))))
    | ~ spl28_98 ),
    inference(resolution,[],[f835,f340])).

fof(f835,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK5(sK17)))
        | v4_funct_1(X0) )
    | ~ spl28_98 ),
    inference(resolution,[],[f833,f278])).

fof(f833,plain,
    ( v4_funct_1(sK5(sK17))
    | ~ spl28_98 ),
    inference(avatar_component_clause,[],[f832])).

fof(f3048,plain,
    ( spl28_442
    | ~ spl28_98 ),
    inference(avatar_split_clause,[],[f3040,f832,f3046])).

fof(f3046,plain,
    ( spl28_442
  <=> v4_funct_1(sK12(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_442])])).

fof(f3040,plain,
    ( v4_funct_1(sK12(sK5(sK17)))
    | ~ spl28_98 ),
    inference(resolution,[],[f835,f343])).

fof(f3027,plain,
    ( spl28_440
    | ~ spl28_96 ),
    inference(avatar_split_clause,[],[f3007,f822,f3025])).

fof(f3025,plain,
    ( spl28_440
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK4(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_440])])).

fof(f822,plain,
    ( spl28_96
  <=> v4_funct_1(sK4(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_96])])).

fof(f3007,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK4(sK17))))
    | ~ spl28_96 ),
    inference(resolution,[],[f825,f340])).

fof(f825,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK4(sK17)))
        | v4_funct_1(X0) )
    | ~ spl28_96 ),
    inference(resolution,[],[f823,f278])).

fof(f823,plain,
    ( v4_funct_1(sK4(sK17))
    | ~ spl28_96 ),
    inference(avatar_component_clause,[],[f822])).

fof(f3017,plain,
    ( spl28_438
    | ~ spl28_96 ),
    inference(avatar_split_clause,[],[f3009,f822,f3015])).

fof(f3015,plain,
    ( spl28_438
  <=> v4_funct_1(sK12(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_438])])).

fof(f3009,plain,
    ( v4_funct_1(sK12(sK4(sK17)))
    | ~ spl28_96 ),
    inference(resolution,[],[f825,f343])).

fof(f2978,plain,
    ( spl28_436
    | ~ spl28_94 ),
    inference(avatar_split_clause,[],[f2958,f812,f2976])).

fof(f2976,plain,
    ( spl28_436
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK3(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_436])])).

fof(f812,plain,
    ( spl28_94
  <=> v4_funct_1(sK3(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_94])])).

fof(f2958,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK3(sK17))))
    | ~ spl28_94 ),
    inference(resolution,[],[f815,f340])).

fof(f815,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK3(sK17)))
        | v4_funct_1(X0) )
    | ~ spl28_94 ),
    inference(resolution,[],[f813,f278])).

fof(f813,plain,
    ( v4_funct_1(sK3(sK17))
    | ~ spl28_94 ),
    inference(avatar_component_clause,[],[f812])).

fof(f2968,plain,
    ( spl28_434
    | ~ spl28_94 ),
    inference(avatar_split_clause,[],[f2960,f812,f2966])).

fof(f2966,plain,
    ( spl28_434
  <=> v4_funct_1(sK12(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_434])])).

fof(f2960,plain,
    ( v4_funct_1(sK12(sK3(sK17)))
    | ~ spl28_94 ),
    inference(resolution,[],[f815,f343])).

fof(f2947,plain,
    ( spl28_432
    | ~ spl28_92 ),
    inference(avatar_split_clause,[],[f2927,f802,f2945])).

fof(f2945,plain,
    ( spl28_432
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK2(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_432])])).

fof(f802,plain,
    ( spl28_92
  <=> v4_funct_1(sK2(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_92])])).

fof(f2927,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK2(sK17))))
    | ~ spl28_92 ),
    inference(resolution,[],[f805,f340])).

fof(f805,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2(sK17)))
        | v4_funct_1(X0) )
    | ~ spl28_92 ),
    inference(resolution,[],[f803,f278])).

fof(f803,plain,
    ( v4_funct_1(sK2(sK17))
    | ~ spl28_92 ),
    inference(avatar_component_clause,[],[f802])).

fof(f2937,plain,
    ( spl28_430
    | ~ spl28_92 ),
    inference(avatar_split_clause,[],[f2929,f802,f2935])).

fof(f2935,plain,
    ( spl28_430
  <=> v4_funct_1(sK12(sK2(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_430])])).

fof(f2929,plain,
    ( v4_funct_1(sK12(sK2(sK17)))
    | ~ spl28_92 ),
    inference(resolution,[],[f805,f343])).

fof(f2916,plain,
    ( spl28_428
    | ~ spl28_88 ),
    inference(avatar_split_clause,[],[f2896,f785,f2914])).

fof(f2914,plain,
    ( spl28_428
  <=> v4_funct_1(sK10(k1_zfmisc_1(sK12(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_428])])).

fof(f785,plain,
    ( spl28_88
  <=> v4_funct_1(sK12(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_88])])).

fof(f2896,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK12(sK17))))
    | ~ spl28_88 ),
    inference(resolution,[],[f788,f340])).

fof(f788,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK12(sK17)))
        | v4_funct_1(X0) )
    | ~ spl28_88 ),
    inference(resolution,[],[f786,f278])).

fof(f786,plain,
    ( v4_funct_1(sK12(sK17))
    | ~ spl28_88 ),
    inference(avatar_component_clause,[],[f785])).

fof(f2906,plain,
    ( spl28_426
    | ~ spl28_88 ),
    inference(avatar_split_clause,[],[f2898,f785,f2904])).

fof(f2904,plain,
    ( spl28_426
  <=> v4_funct_1(sK12(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_426])])).

fof(f2898,plain,
    ( v4_funct_1(sK12(sK12(sK17)))
    | ~ spl28_88 ),
    inference(resolution,[],[f788,f343])).

fof(f2887,plain,
    ( spl28_424
    | ~ spl28_78 ),
    inference(avatar_split_clause,[],[f2869,f688,f2885])).

fof(f2885,plain,
    ( spl28_424
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK10(sK17)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_424])])).

fof(f2869,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK10(sK17))))
    | ~ spl28_78 ),
    inference(resolution,[],[f762,f340])).

fof(f762,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK10(sK17)))
        | v1_relat_1(X2) )
    | ~ spl28_78 ),
    inference(resolution,[],[f287,f689])).

fof(f2879,plain,
    ( spl28_422
    | ~ spl28_78 ),
    inference(avatar_split_clause,[],[f2871,f688,f2877])).

fof(f2877,plain,
    ( spl28_422
  <=> v1_relat_1(sK12(sK10(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_422])])).

fof(f2871,plain,
    ( v1_relat_1(sK12(sK10(sK17)))
    | ~ spl28_78 ),
    inference(resolution,[],[f762,f343])).

fof(f2861,plain,
    ( ~ spl28_421
    | spl28_77
    | ~ spl28_418 ),
    inference(avatar_split_clause,[],[f2854,f2847,f678,f2859])).

fof(f678,plain,
    ( spl28_77
  <=> ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_77])])).

fof(f2854,plain,
    ( ~ v1_subset_1(k1_tarski(sK1),u1_struct_0(sK0))
    | ~ spl28_77
    | ~ spl28_418 ),
    inference(superposition,[],[f679,f2848])).

fof(f679,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl28_77 ),
    inference(avatar_component_clause,[],[f678])).

fof(f2849,plain,
    ( spl28_416
    | spl28_418
    | ~ spl28_70 ),
    inference(avatar_split_clause,[],[f2210,f648,f2847,f2841])).

fof(f2210,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl28_70 ),
    inference(resolution,[],[f348,f649])).

fof(f348,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f187])).

fof(f187,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f78])).

fof(f78,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',redefinition_k6_domain_1)).

fof(f2836,plain,
    ( spl28_414
    | ~ spl28_64
    | ~ spl28_66
    | spl28_183 ),
    inference(avatar_split_clause,[],[f2751,f1258,f634,f627,f2834])).

fof(f2834,plain,
    ( spl28_414
  <=> v1_funct_1(sK9(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_414])])).

fof(f1258,plain,
    ( spl28_183
  <=> ~ v1_zfmisc_1(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_183])])).

fof(f2751,plain,
    ( v1_funct_1(sK9(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_183 ),
    inference(subsumption_resolution,[],[f2742,f1259])).

fof(f1259,plain,
    ( ~ v1_zfmisc_1(sK27)
    | ~ spl28_183 ),
    inference(avatar_component_clause,[],[f1258])).

fof(f2742,plain,
    ( v1_funct_1(sK9(sK27))
    | v1_zfmisc_1(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f395])).

fof(f395,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f314,f263])).

fof(f314,plain,(
    ! [X0] :
      ( m1_subset_1(sK9(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f214])).

fof(f214,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK9(X0),X0)
        & v1_zfmisc_1(sK9(X0))
        & ~ v1_xboole_0(sK9(X0))
        & m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f154,f213])).

fof(f213,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK9(X0),X0)
        & v1_zfmisc_1(sK9(X0))
        & ~ v1_xboole_0(sK9(X0))
        & m1_subset_1(sK9(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f154,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f153])).

fof(f153,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_tex_2)).

fof(f2825,plain,
    ( spl28_412
    | ~ spl28_64
    | ~ spl28_66
    | spl28_183 ),
    inference(avatar_split_clause,[],[f2750,f1258,f634,f627,f2823])).

fof(f2823,plain,
    ( spl28_412
  <=> v1_funct_1(sK8(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_412])])).

fof(f2750,plain,
    ( v1_funct_1(sK8(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_183 ),
    inference(subsumption_resolution,[],[f2741,f1259])).

fof(f2741,plain,
    ( v1_funct_1(sK8(sK27))
    | v1_zfmisc_1(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f391])).

fof(f391,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f310,f263])).

fof(f310,plain,(
    ! [X0] :
      ( m1_subset_1(sK8(X0),k1_zfmisc_1(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f212])).

fof(f212,plain,(
    ! [X0] :
      ( ( ~ v1_subset_1(sK8(X0),X0)
        & ~ v1_zfmisc_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f152,f211])).

fof(f211,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK8(X0),X0)
        & ~ v1_zfmisc_1(sK8(X0))
        & ~ v1_xboole_0(sK8(X0))
        & m1_subset_1(sK8(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f152,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f151])).

fof(f151,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & ~ v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc3_tex_2)).

fof(f2814,plain,
    ( spl28_410
    | ~ spl28_64
    | ~ spl28_66
    | spl28_187 ),
    inference(avatar_split_clause,[],[f2749,f1272,f634,f627,f2812])).

fof(f2812,plain,
    ( spl28_410
  <=> v1_funct_1(sK5(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_410])])).

fof(f2749,plain,
    ( v1_funct_1(sK5(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f2740,f1273])).

fof(f2740,plain,
    ( v1_funct_1(sK5(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f274])).

fof(f274,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f206])).

fof(f206,plain,(
    ! [X0] :
      ( ( v1_subset_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f111,f205])).

fof(f205,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_subset_1(sK5(X0),X0)
        & m1_subset_1(sK5(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f70])).

fof(f70,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc4_subset_1)).

fof(f2803,plain,
    ( spl28_408
    | ~ spl28_64
    | ~ spl28_66
    | spl28_187 ),
    inference(avatar_split_clause,[],[f2748,f1272,f634,f627,f2801])).

fof(f2801,plain,
    ( spl28_408
  <=> v1_funct_1(sK4(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_408])])).

fof(f2748,plain,
    ( v1_funct_1(sK4(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f2739,f1273])).

fof(f2739,plain,
    ( v1_funct_1(sK4(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f271])).

fof(f271,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f204])).

fof(f204,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f110,f203])).

fof(f203,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK4(X0))
        & ~ v1_xboole_0(sK4(X0))
        & m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f110,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f66])).

fof(f66,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc3_realset1)).

fof(f2792,plain,
    ( spl28_406
    | ~ spl28_64
    | ~ spl28_66
    | spl28_187 ),
    inference(avatar_split_clause,[],[f2747,f1272,f634,f627,f2790])).

fof(f2790,plain,
    ( spl28_406
  <=> v1_funct_1(sK3(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_406])])).

fof(f2747,plain,
    ( v1_funct_1(sK3(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f2738,f1273])).

fof(f2738,plain,
    ( v1_funct_1(sK3(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f268])).

fof(f268,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f202])).

fof(f202,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f109,f201])).

fof(f201,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_zfmisc_1(sK3(X0))
        & ~ v1_xboole_0(sK3(X0))
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f59])).

fof(f59,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( v1_zfmisc_1(X1)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_tex_2)).

fof(f2781,plain,
    ( spl28_404
    | ~ spl28_64
    | ~ spl28_66
    | spl28_187 ),
    inference(avatar_split_clause,[],[f2746,f1272,f634,f627,f2779])).

fof(f2779,plain,
    ( spl28_404
  <=> v1_funct_1(sK2(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_404])])).

fof(f2746,plain,
    ( v1_funct_1(sK2(sK27))
    | ~ spl28_64
    | ~ spl28_66
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f2737,f1273])).

fof(f2737,plain,
    ( v1_funct_1(sK2(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f266])).

fof(f266,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f200])).

fof(f200,plain,(
    ! [X0] :
      ( ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f108,f199])).

fof(f199,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_xboole_0(sK2(X0))
        & m1_subset_1(sK2(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f108,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f58])).

fof(f58,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_subset_1)).

fof(f2770,plain,
    ( spl28_402
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(avatar_split_clause,[],[f2743,f634,f627,f2768])).

fof(f2768,plain,
    ( spl28_402
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_402])])).

fof(f2743,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK27)))
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f340])).

fof(f2759,plain,
    ( spl28_400
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(avatar_split_clause,[],[f2745,f634,f627,f2757])).

fof(f2757,plain,
    ( spl28_400
  <=> v1_funct_1(sK12(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_400])])).

fof(f2745,plain,
    ( v1_funct_1(sK12(sK27))
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(resolution,[],[f1858,f343])).

fof(f2731,plain,
    ( spl28_398
    | ~ spl28_58
    | ~ spl28_60
    | spl28_169 ),
    inference(avatar_split_clause,[],[f2639,f1208,f613,f606,f2729])).

fof(f2729,plain,
    ( spl28_398
  <=> v1_funct_1(sK9(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_398])])).

fof(f1208,plain,
    ( spl28_169
  <=> ~ v1_zfmisc_1(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_169])])).

fof(f2639,plain,
    ( v1_funct_1(sK9(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_169 ),
    inference(subsumption_resolution,[],[f2630,f1209])).

fof(f1209,plain,
    ( ~ v1_zfmisc_1(sK26)
    | ~ spl28_169 ),
    inference(avatar_component_clause,[],[f1208])).

fof(f2630,plain,
    ( v1_funct_1(sK9(sK26))
    | v1_zfmisc_1(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f395])).

fof(f2720,plain,
    ( spl28_396
    | ~ spl28_58
    | ~ spl28_60
    | spl28_169 ),
    inference(avatar_split_clause,[],[f2638,f1208,f613,f606,f2718])).

fof(f2718,plain,
    ( spl28_396
  <=> v1_funct_1(sK8(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_396])])).

fof(f2638,plain,
    ( v1_funct_1(sK8(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_169 ),
    inference(subsumption_resolution,[],[f2629,f1209])).

fof(f2629,plain,
    ( v1_funct_1(sK8(sK26))
    | v1_zfmisc_1(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f391])).

fof(f2709,plain,
    ( spl28_394
    | ~ spl28_58
    | ~ spl28_60
    | spl28_73 ),
    inference(avatar_split_clause,[],[f2637,f657,f613,f606,f2707])).

fof(f2707,plain,
    ( spl28_394
  <=> v1_funct_1(sK5(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_394])])).

fof(f2637,plain,
    ( v1_funct_1(sK5(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f2628,f658])).

fof(f2628,plain,
    ( v1_funct_1(sK5(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f274])).

fof(f2698,plain,
    ( spl28_392
    | ~ spl28_58
    | ~ spl28_60
    | spl28_73 ),
    inference(avatar_split_clause,[],[f2636,f657,f613,f606,f2696])).

fof(f2696,plain,
    ( spl28_392
  <=> v1_funct_1(sK4(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_392])])).

fof(f2636,plain,
    ( v1_funct_1(sK4(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f2627,f658])).

fof(f2627,plain,
    ( v1_funct_1(sK4(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f271])).

fof(f2680,plain,
    ( spl28_390
    | ~ spl28_58
    | ~ spl28_60
    | spl28_73 ),
    inference(avatar_split_clause,[],[f2635,f657,f613,f606,f2678])).

fof(f2678,plain,
    ( spl28_390
  <=> v1_funct_1(sK3(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_390])])).

fof(f2635,plain,
    ( v1_funct_1(sK3(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f2626,f658])).

fof(f2626,plain,
    ( v1_funct_1(sK3(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f268])).

fof(f2669,plain,
    ( spl28_388
    | ~ spl28_58
    | ~ spl28_60
    | spl28_73 ),
    inference(avatar_split_clause,[],[f2634,f657,f613,f606,f2667])).

fof(f2667,plain,
    ( spl28_388
  <=> v1_funct_1(sK2(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_388])])).

fof(f2634,plain,
    ( v1_funct_1(sK2(sK26))
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f2625,f658])).

fof(f2625,plain,
    ( v1_funct_1(sK2(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f266])).

fof(f2658,plain,
    ( spl28_386
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(avatar_split_clause,[],[f2631,f613,f606,f2656])).

fof(f2656,plain,
    ( spl28_386
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_386])])).

fof(f2631,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK26)))
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f340])).

fof(f2647,plain,
    ( spl28_384
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(avatar_split_clause,[],[f2633,f613,f606,f2645])).

fof(f2645,plain,
    ( spl28_384
  <=> v1_funct_1(sK12(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_384])])).

fof(f2633,plain,
    ( v1_funct_1(sK12(sK26))
    | ~ spl28_58
    | ~ spl28_60 ),
    inference(resolution,[],[f1857,f343])).

fof(f2623,plain,
    ( spl28_382
    | ~ spl28_228
    | ~ spl28_284
    | ~ spl28_364 ),
    inference(avatar_split_clause,[],[f2484,f2477,f1815,f1513,f2621])).

fof(f2621,plain,
    ( spl28_382
  <=> v3_funct_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_382])])).

fof(f1513,plain,
    ( spl28_228
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_228])])).

fof(f1815,plain,
    ( spl28_284
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_284])])).

fof(f2477,plain,
    ( spl28_364
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK25))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_364])])).

fof(f2484,plain,
    ( v3_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_228
    | ~ spl28_284
    | ~ spl28_364 ),
    inference(subsumption_resolution,[],[f2483,f1514])).

fof(f1514,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_228 ),
    inference(avatar_component_clause,[],[f1513])).

fof(f2483,plain,
    ( v3_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ v1_relat_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_284
    | ~ spl28_364 ),
    inference(subsumption_resolution,[],[f2481,f1816])).

fof(f1816,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_284 ),
    inference(avatar_component_clause,[],[f1815])).

fof(f2481,plain,
    ( v3_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ v1_zfmisc_1(sK10(k1_zfmisc_1(sK25)))
    | ~ v1_relat_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_364 ),
    inference(resolution,[],[f2478,f325])).

fof(f2478,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_364 ),
    inference(avatar_component_clause,[],[f2477])).

fof(f2616,plain,
    ( spl28_380
    | ~ spl28_236
    | ~ spl28_288
    | ~ spl28_378 ),
    inference(avatar_split_clause,[],[f2609,f2602,f1830,f1545,f2614])).

fof(f2614,plain,
    ( spl28_380
  <=> v3_funct_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_380])])).

fof(f1545,plain,
    ( spl28_236
  <=> v1_relat_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_236])])).

fof(f1830,plain,
    ( spl28_288
  <=> v1_zfmisc_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_288])])).

fof(f2602,plain,
    ( spl28_378
  <=> v1_funct_1(sK5(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_378])])).

fof(f2609,plain,
    ( v3_funct_1(sK5(sK25))
    | ~ spl28_236
    | ~ spl28_288
    | ~ spl28_378 ),
    inference(subsumption_resolution,[],[f2608,f1546])).

fof(f1546,plain,
    ( v1_relat_1(sK5(sK25))
    | ~ spl28_236 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f2608,plain,
    ( v3_funct_1(sK5(sK25))
    | ~ v1_relat_1(sK5(sK25))
    | ~ spl28_288
    | ~ spl28_378 ),
    inference(subsumption_resolution,[],[f2606,f1831])).

fof(f1831,plain,
    ( v1_zfmisc_1(sK5(sK25))
    | ~ spl28_288 ),
    inference(avatar_component_clause,[],[f1830])).

fof(f2606,plain,
    ( v3_funct_1(sK5(sK25))
    | ~ v1_zfmisc_1(sK5(sK25))
    | ~ v1_relat_1(sK5(sK25))
    | ~ spl28_378 ),
    inference(resolution,[],[f2603,f325])).

fof(f2603,plain,
    ( v1_funct_1(sK5(sK25))
    | ~ spl28_378 ),
    inference(avatar_component_clause,[],[f2602])).

fof(f2604,plain,
    ( spl28_180
    | spl28_378
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(avatar_split_clause,[],[f2450,f599,f592,f2602,f1248])).

fof(f1248,plain,
    ( spl28_180
  <=> v1_xboole_0(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_180])])).

fof(f2450,plain,
    ( v1_funct_1(sK5(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f274])).

fof(f2597,plain,
    ( spl28_180
    | spl28_370
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(avatar_split_clause,[],[f2449,f599,f592,f2512,f1248])).

fof(f2512,plain,
    ( spl28_370
  <=> v1_funct_1(sK4(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_370])])).

fof(f2449,plain,
    ( v1_funct_1(sK4(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f271])).

fof(f2594,plain,
    ( spl28_376
    | ~ spl28_230
    | ~ spl28_286
    | ~ spl28_366 ),
    inference(avatar_split_clause,[],[f2496,f2489,f1822,f1520,f2592])).

fof(f2592,plain,
    ( spl28_376
  <=> v3_funct_1(sK2(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_376])])).

fof(f1520,plain,
    ( spl28_230
  <=> v1_relat_1(sK2(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_230])])).

fof(f1822,plain,
    ( spl28_286
  <=> v1_zfmisc_1(sK2(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_286])])).

fof(f2489,plain,
    ( spl28_366
  <=> v1_funct_1(sK2(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_366])])).

fof(f2496,plain,
    ( v3_funct_1(sK2(sK25))
    | ~ spl28_230
    | ~ spl28_286
    | ~ spl28_366 ),
    inference(subsumption_resolution,[],[f2495,f1521])).

fof(f1521,plain,
    ( v1_relat_1(sK2(sK25))
    | ~ spl28_230 ),
    inference(avatar_component_clause,[],[f1520])).

fof(f2495,plain,
    ( v3_funct_1(sK2(sK25))
    | ~ v1_relat_1(sK2(sK25))
    | ~ spl28_286
    | ~ spl28_366 ),
    inference(subsumption_resolution,[],[f2493,f1823])).

fof(f1823,plain,
    ( v1_zfmisc_1(sK2(sK25))
    | ~ spl28_286 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f2493,plain,
    ( v3_funct_1(sK2(sK25))
    | ~ v1_zfmisc_1(sK2(sK25))
    | ~ v1_relat_1(sK2(sK25))
    | ~ spl28_366 ),
    inference(resolution,[],[f2490,f325])).

fof(f2490,plain,
    ( v1_funct_1(sK2(sK25))
    | ~ spl28_366 ),
    inference(avatar_component_clause,[],[f2489])).

fof(f2547,plain,
    ( spl28_374
    | ~ spl28_226
    | ~ spl28_282
    | ~ spl28_362 ),
    inference(avatar_split_clause,[],[f2472,f2465,f1807,f1505,f2545])).

fof(f2545,plain,
    ( spl28_374
  <=> v3_funct_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_374])])).

fof(f1505,plain,
    ( spl28_226
  <=> v1_relat_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_226])])).

fof(f1807,plain,
    ( spl28_282
  <=> v1_zfmisc_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_282])])).

fof(f2465,plain,
    ( spl28_362
  <=> v1_funct_1(sK12(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_362])])).

fof(f2472,plain,
    ( v3_funct_1(sK12(sK25))
    | ~ spl28_226
    | ~ spl28_282
    | ~ spl28_362 ),
    inference(subsumption_resolution,[],[f2471,f1506])).

fof(f1506,plain,
    ( v1_relat_1(sK12(sK25))
    | ~ spl28_226 ),
    inference(avatar_component_clause,[],[f1505])).

fof(f2471,plain,
    ( v3_funct_1(sK12(sK25))
    | ~ v1_relat_1(sK12(sK25))
    | ~ spl28_282
    | ~ spl28_362 ),
    inference(subsumption_resolution,[],[f2469,f1808])).

fof(f1808,plain,
    ( v1_zfmisc_1(sK12(sK25))
    | ~ spl28_282 ),
    inference(avatar_component_clause,[],[f1807])).

fof(f2469,plain,
    ( v3_funct_1(sK12(sK25))
    | ~ v1_zfmisc_1(sK12(sK25))
    | ~ v1_relat_1(sK12(sK25))
    | ~ spl28_362 ),
    inference(resolution,[],[f2466,f325])).

fof(f2466,plain,
    ( v1_funct_1(sK12(sK25))
    | ~ spl28_362 ),
    inference(avatar_component_clause,[],[f2465])).

fof(f2536,plain,
    ( spl28_372
    | ~ spl28_180 ),
    inference(avatar_split_clause,[],[f2518,f1248,f2534])).

fof(f2534,plain,
    ( spl28_372
  <=> o_0_0_xboole_0 = sK25 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_372])])).

fof(f2518,plain,
    ( o_0_0_xboole_0 = sK25
    | ~ spl28_180 ),
    inference(resolution,[],[f1249,f385])).

fof(f385,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f295,f258])).

fof(f258,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,axiom,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',d2_xboole_0)).

fof(f295,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f134])).

fof(f134,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',t6_boole)).

fof(f1249,plain,
    ( v1_xboole_0(sK25)
    | ~ spl28_180 ),
    inference(avatar_component_clause,[],[f1248])).

fof(f2514,plain,
    ( spl28_370
    | ~ spl28_54
    | ~ spl28_56
    | spl28_181 ),
    inference(avatar_split_clause,[],[f2458,f1251,f599,f592,f2512])).

fof(f2458,plain,
    ( v1_funct_1(sK4(sK25))
    | ~ spl28_54
    | ~ spl28_56
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f2449,f1252])).

fof(f2503,plain,
    ( spl28_368
    | ~ spl28_54
    | ~ spl28_56
    | spl28_181 ),
    inference(avatar_split_clause,[],[f2457,f1251,f599,f592,f2501])).

fof(f2501,plain,
    ( spl28_368
  <=> v1_funct_1(sK3(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_368])])).

fof(f2457,plain,
    ( v1_funct_1(sK3(sK25))
    | ~ spl28_54
    | ~ spl28_56
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f2448,f1252])).

fof(f2448,plain,
    ( v1_funct_1(sK3(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f268])).

fof(f2491,plain,
    ( spl28_366
    | ~ spl28_54
    | ~ spl28_56
    | spl28_181 ),
    inference(avatar_split_clause,[],[f2456,f1251,f599,f592,f2489])).

fof(f2456,plain,
    ( v1_funct_1(sK2(sK25))
    | ~ spl28_54
    | ~ spl28_56
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f2447,f1252])).

fof(f2447,plain,
    ( v1_funct_1(sK2(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f266])).

fof(f2479,plain,
    ( spl28_364
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(avatar_split_clause,[],[f2453,f599,f592,f2477])).

fof(f2453,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f340])).

fof(f2467,plain,
    ( spl28_362
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(avatar_split_clause,[],[f2455,f599,f592,f2465])).

fof(f2455,plain,
    ( v1_funct_1(sK12(sK25))
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(resolution,[],[f1856,f343])).

fof(f2432,plain,
    ( spl28_360
    | ~ spl28_50
    | ~ spl28_52
    | spl28_171 ),
    inference(avatar_split_clause,[],[f2319,f1216,f585,f578,f2430])).

fof(f2430,plain,
    ( spl28_360
  <=> v1_funct_1(sK9(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_360])])).

fof(f1216,plain,
    ( spl28_171
  <=> ~ v1_zfmisc_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_171])])).

fof(f2319,plain,
    ( v1_funct_1(sK9(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_171 ),
    inference(subsumption_resolution,[],[f2310,f1217])).

fof(f1217,plain,
    ( ~ v1_zfmisc_1(sK24)
    | ~ spl28_171 ),
    inference(avatar_component_clause,[],[f1216])).

fof(f2310,plain,
    ( v1_funct_1(sK9(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f395])).

fof(f2421,plain,
    ( spl28_358
    | ~ spl28_50
    | ~ spl28_52
    | spl28_171 ),
    inference(avatar_split_clause,[],[f2318,f1216,f585,f578,f2419])).

fof(f2419,plain,
    ( spl28_358
  <=> v1_funct_1(sK8(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_358])])).

fof(f2318,plain,
    ( v1_funct_1(sK8(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_171 ),
    inference(subsumption_resolution,[],[f2309,f1217])).

fof(f2309,plain,
    ( v1_funct_1(sK8(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f391])).

fof(f2410,plain,
    ( spl28_356
    | ~ spl28_50
    | ~ spl28_52
    | spl28_175 ),
    inference(avatar_split_clause,[],[f2317,f1230,f585,f578,f2408])).

fof(f2408,plain,
    ( spl28_356
  <=> v1_funct_1(sK5(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_356])])).

fof(f2317,plain,
    ( v1_funct_1(sK5(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f2308,f1231])).

fof(f2308,plain,
    ( v1_funct_1(sK5(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f274])).

fof(f2371,plain,
    ( spl28_354
    | ~ spl28_50
    | ~ spl28_52
    | spl28_175 ),
    inference(avatar_split_clause,[],[f2316,f1230,f585,f578,f2369])).

fof(f2369,plain,
    ( spl28_354
  <=> v1_funct_1(sK4(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_354])])).

fof(f2316,plain,
    ( v1_funct_1(sK4(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f2307,f1231])).

fof(f2307,plain,
    ( v1_funct_1(sK4(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f271])).

fof(f2360,plain,
    ( spl28_352
    | ~ spl28_50
    | ~ spl28_52
    | spl28_175 ),
    inference(avatar_split_clause,[],[f2315,f1230,f585,f578,f2358])).

fof(f2358,plain,
    ( spl28_352
  <=> v1_funct_1(sK3(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_352])])).

fof(f2315,plain,
    ( v1_funct_1(sK3(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f2306,f1231])).

fof(f2306,plain,
    ( v1_funct_1(sK3(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f268])).

fof(f2349,plain,
    ( spl28_350
    | ~ spl28_50
    | ~ spl28_52
    | spl28_175 ),
    inference(avatar_split_clause,[],[f2314,f1230,f585,f578,f2347])).

fof(f2347,plain,
    ( spl28_350
  <=> v1_funct_1(sK2(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_350])])).

fof(f2314,plain,
    ( v1_funct_1(sK2(sK24))
    | ~ spl28_50
    | ~ spl28_52
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f2305,f1231])).

fof(f2305,plain,
    ( v1_funct_1(sK2(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f266])).

fof(f2338,plain,
    ( spl28_348
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(avatar_split_clause,[],[f2311,f585,f578,f2336])).

fof(f2336,plain,
    ( spl28_348
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_348])])).

fof(f2311,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK24)))
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f340])).

fof(f2327,plain,
    ( spl28_346
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(avatar_split_clause,[],[f2313,f585,f578,f2325])).

fof(f2325,plain,
    ( spl28_346
  <=> v1_funct_1(sK12(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_346])])).

fof(f2313,plain,
    ( v1_funct_1(sK12(sK24))
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(resolution,[],[f1855,f343])).

fof(f2299,plain,
    ( spl28_344
    | ~ spl28_28
    | ~ spl28_30
    | spl28_149 ),
    inference(avatar_split_clause,[],[f2189,f1094,f508,f501,f2297])).

fof(f2297,plain,
    ( spl28_344
  <=> v1_funct_1(sK9(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_344])])).

fof(f1094,plain,
    ( spl28_149
  <=> ~ v1_zfmisc_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_149])])).

fof(f2189,plain,
    ( v1_funct_1(sK9(sK19))
    | ~ spl28_28
    | ~ spl28_30
    | ~ spl28_149 ),
    inference(subsumption_resolution,[],[f2180,f1095])).

fof(f1095,plain,
    ( ~ v1_zfmisc_1(sK19)
    | ~ spl28_149 ),
    inference(avatar_component_clause,[],[f1094])).

fof(f2180,plain,
    ( v1_funct_1(sK9(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f395])).

fof(f2288,plain,
    ( spl28_342
    | ~ spl28_28
    | ~ spl28_30
    | spl28_149 ),
    inference(avatar_split_clause,[],[f2188,f1094,f508,f501,f2286])).

fof(f2286,plain,
    ( spl28_342
  <=> v1_funct_1(sK8(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_342])])).

fof(f2188,plain,
    ( v1_funct_1(sK8(sK19))
    | ~ spl28_28
    | ~ spl28_30
    | ~ spl28_149 ),
    inference(subsumption_resolution,[],[f2179,f1095])).

fof(f2179,plain,
    ( v1_funct_1(sK8(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f391])).

fof(f2277,plain,
    ( spl28_340
    | spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2187,f508,f501,f494,f2275])).

fof(f2275,plain,
    ( spl28_340
  <=> v1_funct_1(sK5(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_340])])).

fof(f2187,plain,
    ( v1_funct_1(sK5(sK19))
    | ~ spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f2178,f495])).

fof(f2178,plain,
    ( v1_funct_1(sK5(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f274])).

fof(f2266,plain,
    ( spl28_338
    | spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2186,f508,f501,f494,f2264])).

fof(f2264,plain,
    ( spl28_338
  <=> v1_funct_1(sK4(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_338])])).

fof(f2186,plain,
    ( v1_funct_1(sK4(sK19))
    | ~ spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f2177,f495])).

fof(f2177,plain,
    ( v1_funct_1(sK4(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f271])).

fof(f2255,plain,
    ( spl28_336
    | spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2185,f508,f501,f494,f2253])).

fof(f2253,plain,
    ( spl28_336
  <=> v1_funct_1(sK3(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_336])])).

fof(f2185,plain,
    ( v1_funct_1(sK3(sK19))
    | ~ spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f2176,f495])).

fof(f2176,plain,
    ( v1_funct_1(sK3(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f268])).

fof(f2244,plain,
    ( spl28_334
    | spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2184,f508,f501,f494,f2242])).

fof(f2242,plain,
    ( spl28_334
  <=> v1_funct_1(sK2(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_334])])).

fof(f2184,plain,
    ( v1_funct_1(sK2(sK19))
    | ~ spl28_27
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f2175,f495])).

fof(f2175,plain,
    ( v1_funct_1(sK2(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f266])).

fof(f2208,plain,
    ( spl28_332
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2181,f508,f501,f2206])).

fof(f2206,plain,
    ( spl28_332
  <=> v1_funct_1(sK10(k1_zfmisc_1(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_332])])).

fof(f2181,plain,
    ( v1_funct_1(sK10(k1_zfmisc_1(sK19)))
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f340])).

fof(f2197,plain,
    ( spl28_330
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f2183,f508,f501,f2195])).

fof(f2195,plain,
    ( spl28_330
  <=> v1_funct_1(sK12(sK19)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_330])])).

fof(f2183,plain,
    ( v1_funct_1(sK12(sK19))
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(resolution,[],[f1854,f343])).

fof(f2173,plain,
    ( spl28_218
    | ~ spl28_106
    | ~ spl28_138
    | ~ spl28_214 ),
    inference(avatar_split_clause,[],[f2172,f1427,f1048,f883,f1455])).

fof(f1455,plain,
    ( spl28_218
  <=> v3_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_218])])).

fof(f883,plain,
    ( spl28_106
  <=> v1_relat_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_106])])).

fof(f1048,plain,
    ( spl28_138
  <=> v1_zfmisc_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_138])])).

fof(f1427,plain,
    ( spl28_214
  <=> v1_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_214])])).

fof(f2172,plain,
    ( v3_funct_1(o_0_0_xboole_0)
    | ~ spl28_106
    | ~ spl28_138
    | ~ spl28_214 ),
    inference(subsumption_resolution,[],[f2171,f884])).

fof(f884,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl28_106 ),
    inference(avatar_component_clause,[],[f883])).

fof(f2171,plain,
    ( v3_funct_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl28_138
    | ~ spl28_214 ),
    inference(subsumption_resolution,[],[f2170,f1049])).

fof(f1049,plain,
    ( v1_zfmisc_1(o_0_0_xboole_0)
    | ~ spl28_138 ),
    inference(avatar_component_clause,[],[f1048])).

fof(f2170,plain,
    ( v3_funct_1(o_0_0_xboole_0)
    | ~ v1_zfmisc_1(o_0_0_xboole_0)
    | ~ v1_relat_1(o_0_0_xboole_0)
    | ~ spl28_214 ),
    inference(resolution,[],[f1428,f325])).

fof(f1428,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl28_214 ),
    inference(avatar_component_clause,[],[f1427])).

fof(f2168,plain,
    ( spl28_214
    | ~ spl28_6 ),
    inference(avatar_split_clause,[],[f2155,f424,f1427])).

fof(f424,plain,
    ( spl28_6
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_6])])).

fof(f2155,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl28_6 ),
    inference(resolution,[],[f2146,f663])).

fof(f663,plain,(
    ! [X0] : m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f341,f660])).

fof(f660,plain,(
    ! [X0] : o_0_0_xboole_0 = sK11(X0) ),
    inference(resolution,[],[f385,f342])).

fof(f342,plain,(
    ! [X0] : v1_xboole_0(sK11(X0)) ),
    inference(cnf_transformation,[],[f218])).

fof(f218,plain,(
    ! [X0] :
      ( v1_xboole_0(sK11(X0))
      & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f63,f217])).

fof(f217,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK11(X0))
        & m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_subset_1)).

fof(f341,plain,(
    ! [X0] : m1_subset_1(sK11(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f218])).

fof(f2146,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
        | v1_funct_1(X0) )
    | ~ spl28_6 ),
    inference(resolution,[],[f1851,f425])).

fof(f425,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl28_6 ),
    inference(avatar_component_clause,[],[f424])).

fof(f1851,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(subsumption_resolution,[],[f1843,f292])).

fof(f292,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f131])).

fof(f131,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc1_relat_1)).

fof(f1843,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f329,f291])).

fof(f291,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f130])).

fof(f130,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc1_funct_1)).

fof(f2060,plain,
    ( spl28_328
    | spl28_23
    | ~ spl28_120 ),
    inference(avatar_split_clause,[],[f2019,f948,f480,f2058])).

fof(f2058,plain,
    ( spl28_328
  <=> v1_zfmisc_1(sK5(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_328])])).

fof(f2019,plain,
    ( v1_zfmisc_1(sK5(sK18))
    | ~ spl28_23
    | ~ spl28_120 ),
    inference(subsumption_resolution,[],[f2012,f481])).

fof(f2012,plain,
    ( v1_zfmisc_1(sK5(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_120 ),
    inference(resolution,[],[f957,f274])).

fof(f2042,plain,
    ( spl28_326
    | spl28_23
    | ~ spl28_120 ),
    inference(avatar_split_clause,[],[f2018,f948,f480,f2040])).

fof(f2040,plain,
    ( spl28_326
  <=> v1_zfmisc_1(sK2(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_326])])).

fof(f2018,plain,
    ( v1_zfmisc_1(sK2(sK18))
    | ~ spl28_23
    | ~ spl28_120 ),
    inference(subsumption_resolution,[],[f2009,f481])).

fof(f2009,plain,
    ( v1_zfmisc_1(sK2(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_120 ),
    inference(resolution,[],[f957,f266])).

fof(f2035,plain,
    ( spl28_324
    | ~ spl28_120 ),
    inference(avatar_split_clause,[],[f2015,f948,f2033])).

fof(f2033,plain,
    ( spl28_324
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_324])])).

fof(f2015,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK18)))
    | ~ spl28_120 ),
    inference(resolution,[],[f957,f340])).

fof(f2027,plain,
    ( spl28_322
    | ~ spl28_120 ),
    inference(avatar_split_clause,[],[f2017,f948,f2025])).

fof(f2025,plain,
    ( spl28_322
  <=> v1_zfmisc_1(sK12(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_322])])).

fof(f2017,plain,
    ( v1_zfmisc_1(sK12(sK18))
    | ~ spl28_120 ),
    inference(resolution,[],[f957,f343])).

fof(f2005,plain,
    ( spl28_320
    | spl28_19
    | ~ spl28_100 ),
    inference(avatar_split_clause,[],[f1974,f845,f466,f2003])).

fof(f2003,plain,
    ( spl28_320
  <=> v1_zfmisc_1(sK5(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_320])])).

fof(f1974,plain,
    ( v1_zfmisc_1(sK5(sK17))
    | ~ spl28_19
    | ~ spl28_100 ),
    inference(subsumption_resolution,[],[f1967,f467])).

fof(f1967,plain,
    ( v1_zfmisc_1(sK5(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_100 ),
    inference(resolution,[],[f909,f274])).

fof(f1997,plain,
    ( spl28_318
    | spl28_19
    | ~ spl28_100 ),
    inference(avatar_split_clause,[],[f1973,f845,f466,f1995])).

fof(f1995,plain,
    ( spl28_318
  <=> v1_zfmisc_1(sK2(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_318])])).

fof(f1973,plain,
    ( v1_zfmisc_1(sK2(sK17))
    | ~ spl28_19
    | ~ spl28_100 ),
    inference(subsumption_resolution,[],[f1964,f467])).

fof(f1964,plain,
    ( v1_zfmisc_1(sK2(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_100 ),
    inference(resolution,[],[f909,f266])).

fof(f1990,plain,
    ( spl28_316
    | ~ spl28_100 ),
    inference(avatar_split_clause,[],[f1970,f845,f1988])).

fof(f1988,plain,
    ( spl28_316
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_316])])).

fof(f1970,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl28_100 ),
    inference(resolution,[],[f909,f340])).

fof(f1982,plain,
    ( spl28_314
    | ~ spl28_100 ),
    inference(avatar_split_clause,[],[f1972,f845,f1980])).

fof(f1980,plain,
    ( spl28_314
  <=> v1_zfmisc_1(sK12(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_314])])).

fof(f1972,plain,
    ( v1_zfmisc_1(sK12(sK17))
    | ~ spl28_100 ),
    inference(resolution,[],[f909,f343])).

fof(f1962,plain,
    ( ~ spl28_313
    | spl28_103 ),
    inference(avatar_split_clause,[],[f1955,f848,f1960])).

fof(f1960,plain,
    ( spl28_313
  <=> ~ v1_xboole_0(sK8(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_313])])).

fof(f848,plain,
    ( spl28_103
  <=> ~ v4_funct_1(sK8(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_103])])).

fof(f1955,plain,
    ( ~ v1_xboole_0(sK8(sK17))
    | ~ spl28_103 ),
    inference(resolution,[],[f849,f290])).

fof(f290,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f129])).

fof(f129,plain,(
    ! [X0] :
      ( v4_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f51])).

fof(f51,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v4_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc8_funct_1)).

fof(f849,plain,
    ( ~ v4_funct_1(sK8(sK17))
    | ~ spl28_103 ),
    inference(avatar_component_clause,[],[f848])).

fof(f1954,plain,
    ( spl28_310
    | ~ spl28_102 ),
    inference(avatar_split_clause,[],[f1947,f851,f1952])).

fof(f1952,plain,
    ( spl28_310
  <=> v1_funct_1(sK10(sK8(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_310])])).

fof(f851,plain,
    ( spl28_102
  <=> v4_funct_1(sK8(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_102])])).

fof(f1947,plain,
    ( v1_funct_1(sK10(sK8(sK17)))
    | ~ spl28_102 ),
    inference(resolution,[],[f855,f340])).

fof(f855,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK8(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_102 ),
    inference(resolution,[],[f852,f277])).

fof(f852,plain,
    ( v4_funct_1(sK8(sK17))
    | ~ spl28_102 ),
    inference(avatar_component_clause,[],[f851])).

fof(f1945,plain,
    ( spl28_308
    | ~ spl28_98 ),
    inference(avatar_split_clause,[],[f1938,f832,f1943])).

fof(f1943,plain,
    ( spl28_308
  <=> v1_relat_1(sK10(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_308])])).

fof(f1938,plain,
    ( v1_relat_1(sK10(sK5(sK17)))
    | ~ spl28_98 ),
    inference(resolution,[],[f837,f340])).

fof(f837,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK5(sK17))
        | v1_relat_1(X2) )
    | ~ spl28_98 ),
    inference(resolution,[],[f833,f276])).

fof(f1934,plain,
    ( spl28_306
    | ~ spl28_98 ),
    inference(avatar_split_clause,[],[f1927,f832,f1932])).

fof(f1932,plain,
    ( spl28_306
  <=> v1_funct_1(sK10(sK5(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_306])])).

fof(f1927,plain,
    ( v1_funct_1(sK10(sK5(sK17)))
    | ~ spl28_98 ),
    inference(resolution,[],[f836,f340])).

fof(f836,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK5(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_98 ),
    inference(resolution,[],[f833,f277])).

fof(f1925,plain,
    ( spl28_304
    | ~ spl28_96 ),
    inference(avatar_split_clause,[],[f1918,f822,f1923])).

fof(f1923,plain,
    ( spl28_304
  <=> v1_relat_1(sK10(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_304])])).

fof(f1918,plain,
    ( v1_relat_1(sK10(sK4(sK17)))
    | ~ spl28_96 ),
    inference(resolution,[],[f827,f340])).

fof(f827,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK4(sK17))
        | v1_relat_1(X2) )
    | ~ spl28_96 ),
    inference(resolution,[],[f823,f276])).

fof(f1915,plain,
    ( spl28_302
    | ~ spl28_96 ),
    inference(avatar_split_clause,[],[f1908,f822,f1913])).

fof(f1913,plain,
    ( spl28_302
  <=> v1_funct_1(sK10(sK4(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_302])])).

fof(f1908,plain,
    ( v1_funct_1(sK10(sK4(sK17)))
    | ~ spl28_96 ),
    inference(resolution,[],[f826,f340])).

fof(f826,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK4(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_96 ),
    inference(resolution,[],[f823,f277])).

fof(f1906,plain,
    ( spl28_300
    | ~ spl28_94 ),
    inference(avatar_split_clause,[],[f1899,f812,f1904])).

fof(f1904,plain,
    ( spl28_300
  <=> v1_relat_1(sK10(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_300])])).

fof(f1899,plain,
    ( v1_relat_1(sK10(sK3(sK17)))
    | ~ spl28_94 ),
    inference(resolution,[],[f817,f340])).

fof(f817,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK3(sK17))
        | v1_relat_1(X2) )
    | ~ spl28_94 ),
    inference(resolution,[],[f813,f276])).

fof(f1896,plain,
    ( spl28_298
    | ~ spl28_94 ),
    inference(avatar_split_clause,[],[f1889,f812,f1894])).

fof(f1894,plain,
    ( spl28_298
  <=> v1_funct_1(sK10(sK3(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_298])])).

fof(f1889,plain,
    ( v1_funct_1(sK10(sK3(sK17)))
    | ~ spl28_94 ),
    inference(resolution,[],[f816,f340])).

fof(f816,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK3(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_94 ),
    inference(resolution,[],[f813,f277])).

fof(f1887,plain,
    ( spl28_296
    | ~ spl28_92 ),
    inference(avatar_split_clause,[],[f1880,f802,f1885])).

fof(f1885,plain,
    ( spl28_296
  <=> v1_relat_1(sK10(sK2(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_296])])).

fof(f1880,plain,
    ( v1_relat_1(sK10(sK2(sK17)))
    | ~ spl28_92 ),
    inference(resolution,[],[f807,f340])).

fof(f807,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK2(sK17))
        | v1_relat_1(X2) )
    | ~ spl28_92 ),
    inference(resolution,[],[f803,f276])).

fof(f1877,plain,
    ( spl28_294
    | ~ spl28_92 ),
    inference(avatar_split_clause,[],[f1870,f802,f1875])).

fof(f1875,plain,
    ( spl28_294
  <=> v1_funct_1(sK10(sK2(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_294])])).

fof(f1870,plain,
    ( v1_funct_1(sK10(sK2(sK17)))
    | ~ spl28_92 ),
    inference(resolution,[],[f806,f340])).

fof(f806,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK2(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_92 ),
    inference(resolution,[],[f803,f277])).

fof(f1868,plain,
    ( spl28_292
    | ~ spl28_88 ),
    inference(avatar_split_clause,[],[f1861,f785,f1866])).

fof(f1866,plain,
    ( spl28_292
  <=> v1_relat_1(sK10(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_292])])).

fof(f1861,plain,
    ( v1_relat_1(sK10(sK12(sK17)))
    | ~ spl28_88 ),
    inference(resolution,[],[f790,f340])).

fof(f790,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,sK12(sK17))
        | v1_relat_1(X2) )
    | ~ spl28_88 ),
    inference(resolution,[],[f786,f276])).

fof(f1842,plain,
    ( spl28_290
    | ~ spl28_88 ),
    inference(avatar_split_clause,[],[f1835,f785,f1840])).

fof(f1840,plain,
    ( spl28_290
  <=> v1_funct_1(sK10(sK12(sK17))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_290])])).

fof(f1835,plain,
    ( v1_funct_1(sK10(sK12(sK17)))
    | ~ spl28_88 ),
    inference(resolution,[],[f789,f340])).

fof(f789,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK12(sK17))
        | v1_funct_1(X1) )
    | ~ spl28_88 ),
    inference(resolution,[],[f786,f277])).

fof(f1832,plain,
    ( spl28_288
    | ~ spl28_176
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1801,f1251,f1234,f1830])).

fof(f1801,plain,
    ( v1_zfmisc_1(sK5(sK25))
    | ~ spl28_176
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1794,f1252])).

fof(f1794,plain,
    ( v1_zfmisc_1(sK5(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_176 ),
    inference(resolution,[],[f1556,f274])).

fof(f1824,plain,
    ( spl28_286
    | ~ spl28_176
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1800,f1251,f1234,f1822])).

fof(f1800,plain,
    ( v1_zfmisc_1(sK2(sK25))
    | ~ spl28_176
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1791,f1252])).

fof(f1791,plain,
    ( v1_zfmisc_1(sK2(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_176 ),
    inference(resolution,[],[f1556,f266])).

fof(f1817,plain,
    ( spl28_284
    | ~ spl28_176 ),
    inference(avatar_split_clause,[],[f1797,f1234,f1815])).

fof(f1797,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_176 ),
    inference(resolution,[],[f1556,f340])).

fof(f1809,plain,
    ( spl28_282
    | ~ spl28_176 ),
    inference(avatar_split_clause,[],[f1799,f1234,f1807])).

fof(f1799,plain,
    ( v1_zfmisc_1(sK12(sK25))
    | ~ spl28_176 ),
    inference(resolution,[],[f1556,f343])).

fof(f1787,plain,
    ( spl28_280
    | spl28_33
    | ~ spl28_34 ),
    inference(avatar_split_clause,[],[f1756,f522,f515,f1785])).

fof(f1785,plain,
    ( spl28_280
  <=> v1_zfmisc_1(sK5(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_280])])).

fof(f1756,plain,
    ( v1_zfmisc_1(sK5(sK20))
    | ~ spl28_33
    | ~ spl28_34 ),
    inference(subsumption_resolution,[],[f1749,f516])).

fof(f1749,plain,
    ( v1_zfmisc_1(sK5(sK20))
    | v1_xboole_0(sK20)
    | ~ spl28_34 ),
    inference(resolution,[],[f910,f274])).

fof(f1779,plain,
    ( spl28_278
    | spl28_33
    | ~ spl28_34 ),
    inference(avatar_split_clause,[],[f1755,f522,f515,f1777])).

fof(f1777,plain,
    ( spl28_278
  <=> v1_zfmisc_1(sK2(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_278])])).

fof(f1755,plain,
    ( v1_zfmisc_1(sK2(sK20))
    | ~ spl28_33
    | ~ spl28_34 ),
    inference(subsumption_resolution,[],[f1746,f516])).

fof(f1746,plain,
    ( v1_zfmisc_1(sK2(sK20))
    | v1_xboole_0(sK20)
    | ~ spl28_34 ),
    inference(resolution,[],[f910,f266])).

fof(f1772,plain,
    ( spl28_276
    | ~ spl28_34 ),
    inference(avatar_split_clause,[],[f1752,f522,f1770])).

fof(f1770,plain,
    ( spl28_276
  <=> v1_zfmisc_1(sK10(k1_zfmisc_1(sK20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_276])])).

fof(f1752,plain,
    ( v1_zfmisc_1(sK10(k1_zfmisc_1(sK20)))
    | ~ spl28_34 ),
    inference(resolution,[],[f910,f340])).

fof(f1764,plain,
    ( spl28_274
    | ~ spl28_34 ),
    inference(avatar_split_clause,[],[f1754,f522,f1762])).

fof(f1762,plain,
    ( spl28_274
  <=> v1_zfmisc_1(sK12(sK20)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_274])])).

fof(f1754,plain,
    ( v1_zfmisc_1(sK12(sK20))
    | ~ spl28_34 ),
    inference(resolution,[],[f910,f343])).

fof(f1725,plain,
    ( spl28_272
    | ~ spl28_64
    | spl28_183 ),
    inference(avatar_split_clause,[],[f1662,f1258,f627,f1723])).

fof(f1723,plain,
    ( spl28_272
  <=> v1_relat_1(sK9(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_272])])).

fof(f1662,plain,
    ( v1_relat_1(sK9(sK27))
    | ~ spl28_64
    | ~ spl28_183 ),
    inference(subsumption_resolution,[],[f1653,f1259])).

fof(f1653,plain,
    ( v1_relat_1(sK9(sK27))
    | v1_zfmisc_1(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f395])).

fof(f1717,plain,
    ( spl28_270
    | ~ spl28_64
    | spl28_183 ),
    inference(avatar_split_clause,[],[f1661,f1258,f627,f1715])).

fof(f1715,plain,
    ( spl28_270
  <=> v1_relat_1(sK8(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_270])])).

fof(f1661,plain,
    ( v1_relat_1(sK8(sK27))
    | ~ spl28_64
    | ~ spl28_183 ),
    inference(subsumption_resolution,[],[f1652,f1259])).

fof(f1652,plain,
    ( v1_relat_1(sK8(sK27))
    | v1_zfmisc_1(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f391])).

fof(f1709,plain,
    ( spl28_268
    | ~ spl28_64
    | spl28_187 ),
    inference(avatar_split_clause,[],[f1660,f1272,f627,f1707])).

fof(f1707,plain,
    ( spl28_268
  <=> v1_relat_1(sK5(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_268])])).

fof(f1660,plain,
    ( v1_relat_1(sK5(sK27))
    | ~ spl28_64
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f1651,f1273])).

fof(f1651,plain,
    ( v1_relat_1(sK5(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f274])).

fof(f1701,plain,
    ( spl28_266
    | ~ spl28_64
    | spl28_187 ),
    inference(avatar_split_clause,[],[f1659,f1272,f627,f1699])).

fof(f1699,plain,
    ( spl28_266
  <=> v1_relat_1(sK4(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_266])])).

fof(f1659,plain,
    ( v1_relat_1(sK4(sK27))
    | ~ spl28_64
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f1650,f1273])).

fof(f1650,plain,
    ( v1_relat_1(sK4(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f271])).

fof(f1693,plain,
    ( spl28_264
    | ~ spl28_64
    | spl28_187 ),
    inference(avatar_split_clause,[],[f1658,f1272,f627,f1691])).

fof(f1691,plain,
    ( spl28_264
  <=> v1_relat_1(sK3(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_264])])).

fof(f1658,plain,
    ( v1_relat_1(sK3(sK27))
    | ~ spl28_64
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f1649,f1273])).

fof(f1649,plain,
    ( v1_relat_1(sK3(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f268])).

fof(f1685,plain,
    ( spl28_262
    | ~ spl28_64
    | spl28_187 ),
    inference(avatar_split_clause,[],[f1657,f1272,f627,f1683])).

fof(f1683,plain,
    ( spl28_262
  <=> v1_relat_1(sK2(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_262])])).

fof(f1657,plain,
    ( v1_relat_1(sK2(sK27))
    | ~ spl28_64
    | ~ spl28_187 ),
    inference(subsumption_resolution,[],[f1648,f1273])).

fof(f1648,plain,
    ( v1_relat_1(sK2(sK27))
    | v1_xboole_0(sK27)
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f266])).

fof(f1678,plain,
    ( spl28_260
    | ~ spl28_64 ),
    inference(avatar_split_clause,[],[f1654,f627,f1676])).

fof(f1676,plain,
    ( spl28_260
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK27))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_260])])).

fof(f1654,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK27)))
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f340])).

fof(f1670,plain,
    ( spl28_258
    | ~ spl28_64 ),
    inference(avatar_split_clause,[],[f1656,f627,f1668])).

fof(f1668,plain,
    ( spl28_258
  <=> v1_relat_1(sK12(sK27)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_258])])).

fof(f1656,plain,
    ( v1_relat_1(sK12(sK27))
    | ~ spl28_64 ),
    inference(resolution,[],[f770,f343])).

fof(f1644,plain,
    ( spl28_256
    | ~ spl28_58
    | spl28_169 ),
    inference(avatar_split_clause,[],[f1581,f1208,f606,f1642])).

fof(f1642,plain,
    ( spl28_256
  <=> v1_relat_1(sK9(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_256])])).

fof(f1581,plain,
    ( v1_relat_1(sK9(sK26))
    | ~ spl28_58
    | ~ spl28_169 ),
    inference(subsumption_resolution,[],[f1572,f1209])).

fof(f1572,plain,
    ( v1_relat_1(sK9(sK26))
    | v1_zfmisc_1(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f395])).

fof(f1636,plain,
    ( spl28_254
    | ~ spl28_58
    | spl28_169 ),
    inference(avatar_split_clause,[],[f1580,f1208,f606,f1634])).

fof(f1634,plain,
    ( spl28_254
  <=> v1_relat_1(sK8(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_254])])).

fof(f1580,plain,
    ( v1_relat_1(sK8(sK26))
    | ~ spl28_58
    | ~ spl28_169 ),
    inference(subsumption_resolution,[],[f1571,f1209])).

fof(f1571,plain,
    ( v1_relat_1(sK8(sK26))
    | v1_zfmisc_1(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f391])).

fof(f1628,plain,
    ( spl28_252
    | ~ spl28_58
    | spl28_73 ),
    inference(avatar_split_clause,[],[f1579,f657,f606,f1626])).

fof(f1626,plain,
    ( spl28_252
  <=> v1_relat_1(sK5(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_252])])).

fof(f1579,plain,
    ( v1_relat_1(sK5(sK26))
    | ~ spl28_58
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f1570,f658])).

fof(f1570,plain,
    ( v1_relat_1(sK5(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f274])).

fof(f1620,plain,
    ( spl28_250
    | ~ spl28_58
    | spl28_73 ),
    inference(avatar_split_clause,[],[f1578,f657,f606,f1618])).

fof(f1618,plain,
    ( spl28_250
  <=> v1_relat_1(sK4(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_250])])).

fof(f1578,plain,
    ( v1_relat_1(sK4(sK26))
    | ~ spl28_58
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f1569,f658])).

fof(f1569,plain,
    ( v1_relat_1(sK4(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f271])).

fof(f1612,plain,
    ( spl28_248
    | ~ spl28_58
    | spl28_73 ),
    inference(avatar_split_clause,[],[f1577,f657,f606,f1610])).

fof(f1610,plain,
    ( spl28_248
  <=> v1_relat_1(sK3(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_248])])).

fof(f1577,plain,
    ( v1_relat_1(sK3(sK26))
    | ~ spl28_58
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f1568,f658])).

fof(f1568,plain,
    ( v1_relat_1(sK3(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f268])).

fof(f1604,plain,
    ( spl28_246
    | ~ spl28_58
    | spl28_73 ),
    inference(avatar_split_clause,[],[f1576,f657,f606,f1602])).

fof(f1602,plain,
    ( spl28_246
  <=> v1_relat_1(sK2(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_246])])).

fof(f1576,plain,
    ( v1_relat_1(sK2(sK26))
    | ~ spl28_58
    | ~ spl28_73 ),
    inference(subsumption_resolution,[],[f1567,f658])).

fof(f1567,plain,
    ( v1_relat_1(sK2(sK26))
    | v1_xboole_0(sK26)
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f266])).

fof(f1597,plain,
    ( spl28_244
    | ~ spl28_58 ),
    inference(avatar_split_clause,[],[f1573,f606,f1595])).

fof(f1595,plain,
    ( spl28_244
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK26))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_244])])).

fof(f1573,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK26)))
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f340])).

fof(f1589,plain,
    ( spl28_242
    | ~ spl28_58 ),
    inference(avatar_split_clause,[],[f1575,f606,f1587])).

fof(f1587,plain,
    ( spl28_242
  <=> v1_relat_1(sK12(sK26)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_242])])).

fof(f1575,plain,
    ( v1_relat_1(sK12(sK26))
    | ~ spl28_58 ),
    inference(resolution,[],[f769,f343])).

fof(f1565,plain,
    ( spl28_176
    | spl28_240
    | ~ spl28_54 ),
    inference(avatar_split_clause,[],[f1490,f592,f1563,f1234])).

fof(f1563,plain,
    ( spl28_240
  <=> v1_relat_1(sK9(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_240])])).

fof(f1490,plain,
    ( v1_relat_1(sK9(sK25))
    | v1_zfmisc_1(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f395])).

fof(f1558,plain,
    ( spl28_176
    | spl28_238
    | ~ spl28_54 ),
    inference(avatar_split_clause,[],[f1489,f592,f1553,f1234])).

fof(f1553,plain,
    ( spl28_238
  <=> v1_relat_1(sK8(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_238])])).

fof(f1489,plain,
    ( v1_relat_1(sK8(sK25))
    | v1_zfmisc_1(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f391])).

fof(f1555,plain,
    ( spl28_238
    | ~ spl28_54
    | spl28_177 ),
    inference(avatar_split_clause,[],[f1498,f1237,f592,f1553])).

fof(f1237,plain,
    ( spl28_177
  <=> ~ v1_zfmisc_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_177])])).

fof(f1498,plain,
    ( v1_relat_1(sK8(sK25))
    | ~ spl28_54
    | ~ spl28_177 ),
    inference(subsumption_resolution,[],[f1489,f1238])).

fof(f1238,plain,
    ( ~ v1_zfmisc_1(sK25)
    | ~ spl28_177 ),
    inference(avatar_component_clause,[],[f1237])).

fof(f1547,plain,
    ( spl28_236
    | ~ spl28_54
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1497,f1251,f592,f1545])).

fof(f1497,plain,
    ( v1_relat_1(sK5(sK25))
    | ~ spl28_54
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1488,f1252])).

fof(f1488,plain,
    ( v1_relat_1(sK5(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f274])).

fof(f1539,plain,
    ( spl28_234
    | ~ spl28_54
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1496,f1251,f592,f1537])).

fof(f1537,plain,
    ( spl28_234
  <=> v1_relat_1(sK4(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_234])])).

fof(f1496,plain,
    ( v1_relat_1(sK4(sK25))
    | ~ spl28_54
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1487,f1252])).

fof(f1487,plain,
    ( v1_relat_1(sK4(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f271])).

fof(f1531,plain,
    ( spl28_232
    | ~ spl28_54
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1495,f1251,f592,f1529])).

fof(f1529,plain,
    ( spl28_232
  <=> v1_relat_1(sK3(sK25)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_232])])).

fof(f1495,plain,
    ( v1_relat_1(sK3(sK25))
    | ~ spl28_54
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1486,f1252])).

fof(f1486,plain,
    ( v1_relat_1(sK3(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f268])).

fof(f1522,plain,
    ( spl28_230
    | ~ spl28_54
    | spl28_181 ),
    inference(avatar_split_clause,[],[f1494,f1251,f592,f1520])).

fof(f1494,plain,
    ( v1_relat_1(sK2(sK25))
    | ~ spl28_54
    | ~ spl28_181 ),
    inference(subsumption_resolution,[],[f1485,f1252])).

fof(f1485,plain,
    ( v1_relat_1(sK2(sK25))
    | v1_xboole_0(sK25)
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f266])).

fof(f1515,plain,
    ( spl28_228
    | ~ spl28_54 ),
    inference(avatar_split_clause,[],[f1491,f592,f1513])).

fof(f1491,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK25)))
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f340])).

fof(f1507,plain,
    ( spl28_226
    | ~ spl28_54 ),
    inference(avatar_split_clause,[],[f1493,f592,f1505])).

fof(f1493,plain,
    ( v1_relat_1(sK12(sK25))
    | ~ spl28_54 ),
    inference(resolution,[],[f768,f343])).

fof(f1482,plain,
    ( spl28_170
    | spl28_224
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1352,f578,f1480,f1213])).

fof(f1213,plain,
    ( spl28_170
  <=> v1_zfmisc_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_170])])).

fof(f1480,plain,
    ( spl28_224
  <=> v1_relat_1(sK9(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_224])])).

fof(f1352,plain,
    ( v1_relat_1(sK9(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f395])).

fof(f1474,plain,
    ( spl28_170
    | spl28_222
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1351,f578,f1472,f1213])).

fof(f1472,plain,
    ( spl28_222
  <=> v1_relat_1(sK8(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_222])])).

fof(f1351,plain,
    ( v1_relat_1(sK8(sK24))
    | v1_zfmisc_1(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f391])).

fof(f1466,plain,
    ( spl28_174
    | spl28_220
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1350,f578,f1464,f1227])).

fof(f1227,plain,
    ( spl28_174
  <=> v1_xboole_0(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_174])])).

fof(f1464,plain,
    ( spl28_220
  <=> v1_relat_1(sK5(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_220])])).

fof(f1350,plain,
    ( v1_relat_1(sK5(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f274])).

fof(f1457,plain,
    ( spl28_218
    | ~ spl28_172
    | ~ spl28_210 ),
    inference(avatar_split_clause,[],[f1414,f1395,f1222,f1455])).

fof(f1222,plain,
    ( spl28_172
  <=> v3_funct_1(sK24) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_172])])).

fof(f1395,plain,
    ( spl28_210
  <=> o_0_0_xboole_0 = sK24 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_210])])).

fof(f1414,plain,
    ( v3_funct_1(o_0_0_xboole_0)
    | ~ spl28_172
    | ~ spl28_210 ),
    inference(superposition,[],[f1223,f1396])).

fof(f1396,plain,
    ( o_0_0_xboole_0 = sK24
    | ~ spl28_210 ),
    inference(avatar_component_clause,[],[f1395])).

fof(f1223,plain,
    ( v3_funct_1(sK24)
    | ~ spl28_172 ),
    inference(avatar_component_clause,[],[f1222])).

fof(f1437,plain,
    ( spl28_174
    | spl28_216
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1349,f578,f1435,f1227])).

fof(f1435,plain,
    ( spl28_216
  <=> v1_relat_1(sK4(sK24)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_216])])).

fof(f1349,plain,
    ( v1_relat_1(sK4(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f271])).

fof(f1429,plain,
    ( spl28_214
    | ~ spl28_52
    | ~ spl28_210 ),
    inference(avatar_split_clause,[],[f1411,f1395,f585,f1427])).

fof(f1411,plain,
    ( v1_funct_1(o_0_0_xboole_0)
    | ~ spl28_52
    | ~ spl28_210 ),
    inference(superposition,[],[f586,f1396])).

fof(f1407,plain,
    ( spl28_174
    | spl28_212
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1348,f578,f1405,f1227])).

fof(f1348,plain,
    ( v1_relat_1(sK3(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f268])).

fof(f1400,plain,
    ( spl28_174
    | spl28_208
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1347,f578,f1382,f1227])).

fof(f1347,plain,
    ( v1_relat_1(sK2(sK24))
    | v1_xboole_0(sK24)
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f266])).

fof(f1397,plain,
    ( spl28_210
    | ~ spl28_174 ),
    inference(avatar_split_clause,[],[f1390,f1227,f1395])).

fof(f1390,plain,
    ( o_0_0_xboole_0 = sK24
    | ~ spl28_174 ),
    inference(resolution,[],[f1228,f385])).

fof(f1228,plain,
    ( v1_xboole_0(sK24)
    | ~ spl28_174 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1384,plain,
    ( spl28_208
    | ~ spl28_50
    | spl28_175 ),
    inference(avatar_split_clause,[],[f1356,f1230,f578,f1382])).

fof(f1356,plain,
    ( v1_relat_1(sK2(sK24))
    | ~ spl28_50
    | ~ spl28_175 ),
    inference(subsumption_resolution,[],[f1347,f1231])).

fof(f1377,plain,
    ( spl28_206
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1353,f578,f1375])).

fof(f1375,plain,
    ( spl28_206
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK24))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_206])])).

fof(f1353,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK24)))
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f340])).

fof(f1369,plain,
    ( spl28_204
    | ~ spl28_50 ),
    inference(avatar_split_clause,[],[f1355,f578,f1367])).

fof(f1355,plain,
    ( v1_relat_1(sK12(sK24))
    | ~ spl28_50 ),
    inference(resolution,[],[f767,f343])).

fof(f1345,plain,
    ( spl28_198
    | spl28_202
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1129,f571,f1343,f1329])).

fof(f1329,plain,
    ( spl28_198
  <=> v1_zfmisc_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_198])])).

fof(f1343,plain,
    ( spl28_202
  <=> v1_relat_1(sK9(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_202])])).

fof(f571,plain,
    ( spl28_48
  <=> v1_relat_1(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_48])])).

fof(f1129,plain,
    ( v1_relat_1(sK9(sK23))
    | v1_zfmisc_1(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f395])).

fof(f766,plain,
    ( ! [X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(sK23))
        | v1_relat_1(X6) )
    | ~ spl28_48 ),
    inference(resolution,[],[f287,f572])).

fof(f572,plain,
    ( v1_relat_1(sK23)
    | ~ spl28_48 ),
    inference(avatar_component_clause,[],[f571])).

fof(f1337,plain,
    ( spl28_198
    | spl28_200
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1128,f571,f1335,f1329])).

fof(f1335,plain,
    ( spl28_200
  <=> v1_relat_1(sK8(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_200])])).

fof(f1128,plain,
    ( v1_relat_1(sK8(sK23))
    | v1_zfmisc_1(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f391])).

fof(f1324,plain,
    ( spl28_160
    | spl28_196
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1127,f571,f1322,f1154])).

fof(f1154,plain,
    ( spl28_160
  <=> v1_xboole_0(sK23) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_160])])).

fof(f1322,plain,
    ( spl28_196
  <=> v1_relat_1(sK5(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_196])])).

fof(f1127,plain,
    ( v1_relat_1(sK5(sK23))
    | v1_xboole_0(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f274])).

fof(f1317,plain,
    ( spl28_160
    | spl28_194
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1126,f571,f1315,f1154])).

fof(f1315,plain,
    ( spl28_194
  <=> v1_relat_1(sK4(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_194])])).

fof(f1126,plain,
    ( v1_relat_1(sK4(sK23))
    | v1_xboole_0(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f271])).

fof(f1310,plain,
    ( ~ spl28_193
    | spl28_191 ),
    inference(avatar_split_clause,[],[f1303,f1295,f1308])).

fof(f1308,plain,
    ( spl28_193
  <=> ~ v1_xboole_0(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_193])])).

fof(f1295,plain,
    ( spl28_191
  <=> ~ v1_relat_1(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_191])])).

fof(f1303,plain,
    ( ~ v1_xboole_0(sK2(o_0_0_xboole_0))
    | ~ spl28_191 ),
    inference(resolution,[],[f1296,f292])).

fof(f1296,plain,
    ( ~ v1_relat_1(sK2(o_0_0_xboole_0))
    | ~ spl28_191 ),
    inference(avatar_component_clause,[],[f1295])).

fof(f1302,plain,
    ( ~ spl28_191
    | spl28_163
    | ~ spl28_164 ),
    inference(avatar_split_clause,[],[f1301,f1189,f1157,f1295])).

fof(f1157,plain,
    ( spl28_163
  <=> ~ v1_relat_1(sK2(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_163])])).

fof(f1189,plain,
    ( spl28_164
  <=> o_0_0_xboole_0 = sK23 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_164])])).

fof(f1301,plain,
    ( ~ v1_relat_1(sK2(o_0_0_xboole_0))
    | ~ spl28_163
    | ~ spl28_164 ),
    inference(forward_demodulation,[],[f1158,f1190])).

fof(f1190,plain,
    ( o_0_0_xboole_0 = sK23
    | ~ spl28_164 ),
    inference(avatar_component_clause,[],[f1189])).

fof(f1158,plain,
    ( ~ v1_relat_1(sK2(sK23))
    | ~ spl28_163 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1300,plain,
    ( spl28_190
    | ~ spl28_162
    | ~ spl28_164 ),
    inference(avatar_split_clause,[],[f1284,f1189,f1160,f1298])).

fof(f1298,plain,
    ( spl28_190
  <=> v1_relat_1(sK2(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_190])])).

fof(f1160,plain,
    ( spl28_162
  <=> v1_relat_1(sK2(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_162])])).

fof(f1284,plain,
    ( v1_relat_1(sK2(o_0_0_xboole_0))
    | ~ spl28_162
    | ~ spl28_164 ),
    inference(superposition,[],[f1161,f1190])).

fof(f1161,plain,
    ( v1_relat_1(sK2(sK23))
    | ~ spl28_162 ),
    inference(avatar_component_clause,[],[f1160])).

fof(f1282,plain,
    ( spl28_160
    | spl28_188
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1125,f571,f1280,f1154])).

fof(f1280,plain,
    ( spl28_188
  <=> v1_relat_1(sK3(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_188])])).

fof(f1125,plain,
    ( v1_relat_1(sK3(sK23))
    | v1_xboole_0(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f268])).

fof(f1275,plain,
    ( ~ spl28_149
    | spl28_166
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(avatar_split_clause,[],[f1200,f508,f501,f1197,f1094])).

fof(f1197,plain,
    ( spl28_166
  <=> v3_funct_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_166])])).

fof(f1200,plain,
    ( v3_funct_1(sK19)
    | ~ v1_zfmisc_1(sK19)
    | ~ spl28_28
    | ~ spl28_30 ),
    inference(subsumption_resolution,[],[f1171,f502])).

fof(f1171,plain,
    ( v3_funct_1(sK19)
    | ~ v1_zfmisc_1(sK19)
    | ~ v1_relat_1(sK19)
    | ~ spl28_30 ),
    inference(resolution,[],[f325,f509])).

fof(f1274,plain,
    ( ~ spl28_187
    | spl28_183 ),
    inference(avatar_split_clause,[],[f1267,f1258,f1272])).

fof(f1267,plain,
    ( ~ v1_xboole_0(sK27)
    | ~ spl28_183 ),
    inference(resolution,[],[f1259,f263])).

fof(f1266,plain,
    ( ~ spl28_183
    | spl28_184
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(avatar_split_clause,[],[f1184,f634,f627,f1264,f1258])).

fof(f1264,plain,
    ( spl28_184
  <=> v3_funct_1(sK27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_184])])).

fof(f1184,plain,
    ( v3_funct_1(sK27)
    | ~ v1_zfmisc_1(sK27)
    | ~ spl28_64
    | ~ spl28_66 ),
    inference(subsumption_resolution,[],[f1175,f628])).

fof(f1175,plain,
    ( v3_funct_1(sK27)
    | ~ v1_zfmisc_1(sK27)
    | ~ v1_relat_1(sK27)
    | ~ spl28_66 ),
    inference(resolution,[],[f325,f635])).

fof(f1253,plain,
    ( ~ spl28_181
    | spl28_177 ),
    inference(avatar_split_clause,[],[f1246,f1237,f1251])).

fof(f1246,plain,
    ( ~ v1_xboole_0(sK25)
    | ~ spl28_177 ),
    inference(resolution,[],[f1238,f263])).

fof(f1245,plain,
    ( ~ spl28_177
    | spl28_178
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(avatar_split_clause,[],[f1181,f599,f592,f1243,f1237])).

fof(f1243,plain,
    ( spl28_178
  <=> v3_funct_1(sK25) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_178])])).

fof(f1181,plain,
    ( v3_funct_1(sK25)
    | ~ v1_zfmisc_1(sK25)
    | ~ spl28_54
    | ~ spl28_56 ),
    inference(subsumption_resolution,[],[f1173,f593])).

fof(f1173,plain,
    ( v3_funct_1(sK25)
    | ~ v1_zfmisc_1(sK25)
    | ~ v1_relat_1(sK25)
    | ~ spl28_56 ),
    inference(resolution,[],[f325,f600])).

fof(f1232,plain,
    ( ~ spl28_175
    | spl28_171 ),
    inference(avatar_split_clause,[],[f1225,f1216,f1230])).

fof(f1225,plain,
    ( ~ v1_xboole_0(sK24)
    | ~ spl28_171 ),
    inference(resolution,[],[f1217,f263])).

fof(f1224,plain,
    ( ~ spl28_171
    | spl28_172
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(avatar_split_clause,[],[f1180,f585,f578,f1222,f1216])).

fof(f1180,plain,
    ( v3_funct_1(sK24)
    | ~ v1_zfmisc_1(sK24)
    | ~ spl28_50
    | ~ spl28_52 ),
    inference(subsumption_resolution,[],[f1172,f579])).

fof(f1172,plain,
    ( v3_funct_1(sK24)
    | ~ v1_zfmisc_1(sK24)
    | ~ v1_relat_1(sK24)
    | ~ spl28_52 ),
    inference(resolution,[],[f325,f586])).

fof(f1210,plain,
    ( ~ spl28_169
    | ~ spl28_58
    | ~ spl28_60
    | spl28_63 ),
    inference(avatar_split_clause,[],[f1183,f620,f613,f606,f1208])).

fof(f620,plain,
    ( spl28_63
  <=> ~ v3_funct_1(sK26) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_63])])).

fof(f1183,plain,
    ( ~ v1_zfmisc_1(sK26)
    | ~ spl28_58
    | ~ spl28_60
    | ~ spl28_63 ),
    inference(subsumption_resolution,[],[f1182,f607])).

fof(f1182,plain,
    ( ~ v1_zfmisc_1(sK26)
    | ~ v1_relat_1(sK26)
    | ~ spl28_60
    | ~ spl28_63 ),
    inference(subsumption_resolution,[],[f1174,f621])).

fof(f621,plain,
    ( ~ v3_funct_1(sK26)
    | ~ spl28_63 ),
    inference(avatar_component_clause,[],[f620])).

fof(f1174,plain,
    ( v3_funct_1(sK26)
    | ~ v1_zfmisc_1(sK26)
    | ~ v1_relat_1(sK26)
    | ~ spl28_60 ),
    inference(resolution,[],[f325,f614])).

fof(f1199,plain,
    ( spl28_166
    | ~ spl28_28
    | ~ spl28_30
    | ~ spl28_148 ),
    inference(avatar_split_clause,[],[f1179,f1097,f508,f501,f1197])).

fof(f1097,plain,
    ( spl28_148
  <=> v1_zfmisc_1(sK19) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_148])])).

fof(f1179,plain,
    ( v3_funct_1(sK19)
    | ~ spl28_28
    | ~ spl28_30
    | ~ spl28_148 ),
    inference(subsumption_resolution,[],[f1178,f502])).

fof(f1178,plain,
    ( v3_funct_1(sK19)
    | ~ v1_relat_1(sK19)
    | ~ spl28_30
    | ~ spl28_148 ),
    inference(subsumption_resolution,[],[f1171,f1098])).

fof(f1098,plain,
    ( v1_zfmisc_1(sK19)
    | ~ spl28_148 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1191,plain,
    ( spl28_164
    | ~ spl28_160 ),
    inference(avatar_split_clause,[],[f1167,f1154,f1189])).

fof(f1167,plain,
    ( o_0_0_xboole_0 = sK23
    | ~ spl28_160 ),
    inference(resolution,[],[f1155,f385])).

fof(f1155,plain,
    ( v1_xboole_0(sK23)
    | ~ spl28_160 ),
    inference(avatar_component_clause,[],[f1154])).

fof(f1162,plain,
    ( spl28_160
    | spl28_162
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1124,f571,f1160,f1154])).

fof(f1124,plain,
    ( v1_relat_1(sK2(sK23))
    | v1_xboole_0(sK23)
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f266])).

fof(f1148,plain,
    ( spl28_158
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1130,f571,f1146])).

fof(f1146,plain,
    ( spl28_158
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK23))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_158])])).

fof(f1130,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK23)))
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f340])).

fof(f1140,plain,
    ( spl28_156
    | ~ spl28_48 ),
    inference(avatar_split_clause,[],[f1132,f571,f1138])).

fof(f1138,plain,
    ( spl28_156
  <=> v1_relat_1(sK12(sK23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_156])])).

fof(f1132,plain,
    ( v1_relat_1(sK12(sK23))
    | ~ spl28_48 ),
    inference(resolution,[],[f766,f343])).

fof(f1120,plain,
    ( spl28_154
    | ~ spl28_142 ),
    inference(avatar_split_clause,[],[f1075,f1063,f1118])).

fof(f1118,plain,
    ( spl28_154
  <=> o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_154])])).

fof(f1063,plain,
    ( spl28_142
  <=> v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_142])])).

fof(f1075,plain,
    ( o_0_0_xboole_0 = sK10(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl28_142 ),
    inference(resolution,[],[f1064,f385])).

fof(f1064,plain,
    ( v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl28_142 ),
    inference(avatar_component_clause,[],[f1063])).

fof(f1113,plain,
    ( spl28_148
    | spl28_152
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f971,f501,f1111,f1097])).

fof(f971,plain,
    ( v1_relat_1(sK9(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f395])).

fof(f1105,plain,
    ( spl28_148
    | spl28_150
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f970,f501,f1103,f1097])).

fof(f970,plain,
    ( v1_relat_1(sK8(sK19))
    | v1_zfmisc_1(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f391])).

fof(f1092,plain,
    ( ~ spl28_147
    | ~ spl28_144 ),
    inference(avatar_split_clause,[],[f1085,f1080,f1090])).

fof(f1090,plain,
    ( spl28_147
  <=> ~ v1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_147])])).

fof(f1080,plain,
    ( spl28_144
  <=> o_0_0_xboole_0 = sK12(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_144])])).

fof(f1085,plain,
    ( ~ v1_subset_1(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl28_144 ),
    inference(superposition,[],[f344,f1081])).

fof(f1081,plain,
    ( o_0_0_xboole_0 = sK12(o_0_0_xboole_0)
    | ~ spl28_144 ),
    inference(avatar_component_clause,[],[f1080])).

fof(f344,plain,(
    ! [X0] : ~ v1_subset_1(sK12(X0),X0) ),
    inference(cnf_transformation,[],[f220])).

fof(f1082,plain,
    ( spl28_144
    | ~ spl28_140 ),
    inference(avatar_split_clause,[],[f1070,f1055,f1080])).

fof(f1055,plain,
    ( spl28_140
  <=> v1_xboole_0(sK12(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_140])])).

fof(f1070,plain,
    ( o_0_0_xboole_0 = sK12(o_0_0_xboole_0)
    | ~ spl28_140 ),
    inference(resolution,[],[f1056,f385])).

fof(f1056,plain,
    ( v1_xboole_0(sK12(o_0_0_xboole_0))
    | ~ spl28_140 ),
    inference(avatar_component_clause,[],[f1055])).

fof(f1065,plain,(
    spl28_142 ),
    inference(avatar_split_clause,[],[f1040,f1063])).

fof(f1040,plain,(
    v1_xboole_0(sK10(k1_zfmisc_1(o_0_0_xboole_0))) ),
    inference(resolution,[],[f1030,f340])).

fof(f1030,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(o_0_0_xboole_0))
      | v1_xboole_0(X0) ) ),
    inference(forward_demodulation,[],[f1027,f660])).

fof(f1027,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK11(X1)))
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f296,f342])).

fof(f296,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f135])).

fof(f135,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc1_subset_1)).

fof(f1057,plain,(
    spl28_140 ),
    inference(avatar_split_clause,[],[f1042,f1055])).

fof(f1042,plain,(
    v1_xboole_0(sK12(o_0_0_xboole_0)) ),
    inference(resolution,[],[f1030,f343])).

fof(f1050,plain,(
    spl28_138 ),
    inference(avatar_split_clause,[],[f1043,f1048])).

fof(f1043,plain,(
    v1_zfmisc_1(o_0_0_xboole_0) ),
    inference(subsumption_resolution,[],[f1038,f390])).

fof(f390,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK8(X0))
      | v1_zfmisc_1(X0) ) ),
    inference(subsumption_resolution,[],[f311,f263])).

fof(f311,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK8(X0))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f212])).

fof(f1038,plain,
    ( v1_xboole_0(sK8(o_0_0_xboole_0))
    | v1_zfmisc_1(o_0_0_xboole_0) ),
    inference(resolution,[],[f1030,f391])).

fof(f1025,plain,
    ( spl28_136
    | spl28_27
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f978,f501,f494,f1023])).

fof(f978,plain,
    ( v1_relat_1(sK5(sK19))
    | ~ spl28_27
    | ~ spl28_28 ),
    inference(subsumption_resolution,[],[f969,f495])).

fof(f969,plain,
    ( v1_relat_1(sK5(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f274])).

fof(f1017,plain,
    ( spl28_134
    | spl28_27
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f977,f501,f494,f1015])).

fof(f977,plain,
    ( v1_relat_1(sK4(sK19))
    | ~ spl28_27
    | ~ spl28_28 ),
    inference(subsumption_resolution,[],[f968,f495])).

fof(f968,plain,
    ( v1_relat_1(sK4(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f271])).

fof(f1009,plain,
    ( spl28_132
    | spl28_27
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f976,f501,f494,f1007])).

fof(f976,plain,
    ( v1_relat_1(sK3(sK19))
    | ~ spl28_27
    | ~ spl28_28 ),
    inference(subsumption_resolution,[],[f967,f495])).

fof(f967,plain,
    ( v1_relat_1(sK3(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f268])).

fof(f1001,plain,
    ( spl28_130
    | spl28_27
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f975,f501,f494,f999])).

fof(f975,plain,
    ( v1_relat_1(sK2(sK19))
    | ~ spl28_27
    | ~ spl28_28 ),
    inference(subsumption_resolution,[],[f966,f495])).

fof(f966,plain,
    ( v1_relat_1(sK2(sK19))
    | v1_xboole_0(sK19)
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f266])).

fof(f994,plain,
    ( spl28_128
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f972,f501,f992])).

fof(f992,plain,
    ( spl28_128
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK19))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_128])])).

fof(f972,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK19)))
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f340])).

fof(f986,plain,
    ( spl28_126
    | ~ spl28_28 ),
    inference(avatar_split_clause,[],[f974,f501,f984])).

fof(f974,plain,
    ( v1_relat_1(sK12(sK19))
    | ~ spl28_28 ),
    inference(resolution,[],[f765,f343])).

fof(f964,plain,
    ( spl28_120
    | spl28_124
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f870,f487,f962,f948])).

fof(f962,plain,
    ( spl28_124
  <=> v1_relat_1(sK9(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_124])])).

fof(f870,plain,
    ( v1_relat_1(sK9(sK18))
    | v1_zfmisc_1(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f395])).

fof(f956,plain,
    ( spl28_120
    | spl28_122
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f869,f487,f954,f948])).

fof(f954,plain,
    ( spl28_122
  <=> v1_relat_1(sK8(sK18)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_122])])).

fof(f869,plain,
    ( v1_relat_1(sK8(sK18))
    | v1_zfmisc_1(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f391])).

fof(f941,plain,
    ( spl28_118
    | spl28_23
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f877,f487,f480,f939])).

fof(f877,plain,
    ( v1_relat_1(sK5(sK18))
    | ~ spl28_23
    | ~ spl28_24 ),
    inference(subsumption_resolution,[],[f868,f481])).

fof(f868,plain,
    ( v1_relat_1(sK5(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f274])).

fof(f933,plain,
    ( spl28_116
    | spl28_23
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f876,f487,f480,f931])).

fof(f876,plain,
    ( v1_relat_1(sK4(sK18))
    | ~ spl28_23
    | ~ spl28_24 ),
    inference(subsumption_resolution,[],[f867,f481])).

fof(f867,plain,
    ( v1_relat_1(sK4(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f271])).

fof(f925,plain,
    ( spl28_114
    | spl28_23
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f875,f487,f480,f923])).

fof(f875,plain,
    ( v1_relat_1(sK3(sK18))
    | ~ spl28_23
    | ~ spl28_24 ),
    inference(subsumption_resolution,[],[f866,f481])).

fof(f866,plain,
    ( v1_relat_1(sK3(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f268])).

fof(f917,plain,
    ( spl28_112
    | spl28_23
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f874,f487,f480,f915])).

fof(f874,plain,
    ( v1_relat_1(sK2(sK18))
    | ~ spl28_23
    | ~ spl28_24 ),
    inference(subsumption_resolution,[],[f865,f481])).

fof(f865,plain,
    ( v1_relat_1(sK2(sK18))
    | v1_xboole_0(sK18)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f266])).

fof(f901,plain,
    ( spl28_110
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f871,f487,f899])).

fof(f899,plain,
    ( spl28_110
  <=> v1_relat_1(sK10(k1_zfmisc_1(sK18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_110])])).

fof(f871,plain,
    ( v1_relat_1(sK10(k1_zfmisc_1(sK18)))
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f340])).

fof(f893,plain,
    ( spl28_108
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f873,f487,f891])).

fof(f873,plain,
    ( v1_relat_1(sK12(sK18))
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f343])).

fof(f885,plain,
    ( spl28_106
    | ~ spl28_24 ),
    inference(avatar_split_clause,[],[f864,f487,f883])).

fof(f864,plain,
    ( v1_relat_1(o_0_0_xboole_0)
    | ~ spl28_24 ),
    inference(resolution,[],[f764,f663])).

fof(f863,plain,
    ( spl28_100
    | spl28_104
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f752,f473,f861,f845])).

fof(f861,plain,
    ( spl28_104
  <=> v4_funct_1(sK9(sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_104])])).

fof(f752,plain,
    ( v4_funct_1(sK9(sK17))
    | v1_zfmisc_1(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f395])).

fof(f853,plain,
    ( spl28_100
    | spl28_102
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f751,f473,f851,f845])).

fof(f751,plain,
    ( v4_funct_1(sK8(sK17))
    | v1_zfmisc_1(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f391])).

fof(f834,plain,
    ( spl28_98
    | spl28_19
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f759,f473,f466,f832])).

fof(f759,plain,
    ( v4_funct_1(sK5(sK17))
    | ~ spl28_19
    | ~ spl28_20 ),
    inference(subsumption_resolution,[],[f750,f467])).

fof(f750,plain,
    ( v4_funct_1(sK5(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f274])).

fof(f824,plain,
    ( spl28_96
    | spl28_19
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f758,f473,f466,f822])).

fof(f758,plain,
    ( v4_funct_1(sK4(sK17))
    | ~ spl28_19
    | ~ spl28_20 ),
    inference(subsumption_resolution,[],[f749,f467])).

fof(f749,plain,
    ( v4_funct_1(sK4(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f271])).

fof(f814,plain,
    ( spl28_94
    | spl28_19
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f757,f473,f466,f812])).

fof(f757,plain,
    ( v4_funct_1(sK3(sK17))
    | ~ spl28_19
    | ~ spl28_20 ),
    inference(subsumption_resolution,[],[f748,f467])).

fof(f748,plain,
    ( v4_funct_1(sK3(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f268])).

fof(f804,plain,
    ( spl28_92
    | spl28_19
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f756,f473,f466,f802])).

fof(f756,plain,
    ( v4_funct_1(sK2(sK17))
    | ~ spl28_19
    | ~ spl28_20 ),
    inference(subsumption_resolution,[],[f747,f467])).

fof(f747,plain,
    ( v4_funct_1(sK2(sK17))
    | v1_xboole_0(sK17)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f266])).

fof(f797,plain,
    ( spl28_90
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f753,f473,f795])).

fof(f753,plain,
    ( v4_funct_1(sK10(k1_zfmisc_1(sK17)))
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f340])).

fof(f787,plain,
    ( spl28_88
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f755,f473,f785])).

fof(f755,plain,
    ( v4_funct_1(sK12(sK17))
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f343])).

fof(f777,plain,
    ( spl28_86
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f746,f473,f775])).

fof(f775,plain,
    ( spl28_86
  <=> v4_funct_1(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_86])])).

fof(f746,plain,
    ( v4_funct_1(o_0_0_xboole_0)
    | ~ spl28_20 ),
    inference(resolution,[],[f743,f663])).

fof(f739,plain,(
    spl28_84 ),
    inference(avatar_split_clause,[],[f732,f737])).

fof(f737,plain,
    ( spl28_84
  <=> v1_funct_1(sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_84])])).

fof(f732,plain,(
    v1_funct_1(sK10(o_0_0_xboole_0)) ),
    inference(resolution,[],[f730,f340])).

fof(f730,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,o_0_0_xboole_0)
      | v1_funct_1(X0) ) ),
    inference(forward_demodulation,[],[f727,f660])).

fof(f727,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X0)
      | ~ m1_subset_1(X0,sK11(X1)) ) ),
    inference(resolution,[],[f692,f342])).

fof(f692,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | v1_funct_1(X1)
      | ~ m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f277,f290])).

fof(f726,plain,(
    spl28_82 ),
    inference(avatar_split_clause,[],[f719,f724])).

fof(f724,plain,
    ( spl28_82
  <=> v1_relat_1(sK10(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_82])])).

fof(f719,plain,(
    v1_relat_1(sK10(o_0_0_xboole_0)) ),
    inference(resolution,[],[f717,f340])).

fof(f717,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,o_0_0_xboole_0)
      | v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f714,f660])).

fof(f714,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
      | ~ m1_subset_1(X0,sK11(X1)) ) ),
    inference(resolution,[],[f682,f342])).

fof(f682,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X2)
      | v1_relat_1(X1)
      | ~ m1_subset_1(X1,X2) ) ),
    inference(resolution,[],[f276,f290])).

fof(f700,plain,
    ( spl28_80
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f693,f473,f698])).

fof(f693,plain,
    ( v1_funct_1(sK10(sK17))
    | ~ spl28_20 ),
    inference(resolution,[],[f691,f340])).

fof(f691,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK17)
        | v1_funct_1(X0) )
    | ~ spl28_20 ),
    inference(resolution,[],[f277,f474])).

fof(f690,plain,
    ( spl28_78
    | ~ spl28_20 ),
    inference(avatar_split_clause,[],[f683,f473,f688])).

fof(f683,plain,
    ( v1_relat_1(sK10(sK17))
    | ~ spl28_20 ),
    inference(resolution,[],[f681,f340])).

fof(f681,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK17)
        | v1_relat_1(X0) )
    | ~ spl28_20 ),
    inference(resolution,[],[f276,f474])).

fof(f680,plain,(
    ~ spl28_77 ),
    inference(avatar_split_clause,[],[f255,f678])).

fof(f255,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f198])).

fof(f198,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v7_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f101,f197,f196])).

fof(f196,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v7_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f197,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),sK1),u1_struct_0(X0))
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f101,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f100])).

fof(f100,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',t9_tex_2)).

fof(f671,plain,
    ( spl28_74
    | ~ spl28_12 ),
    inference(avatar_split_clause,[],[f662,f445,f669])).

fof(f669,plain,
    ( spl28_74
  <=> o_0_0_xboole_0 = sK15 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_74])])).

fof(f445,plain,
    ( spl28_12
  <=> v1_xboole_0(sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_12])])).

fof(f662,plain,
    ( o_0_0_xboole_0 = sK15
    | ~ spl28_12 ),
    inference(resolution,[],[f385,f446])).

fof(f446,plain,
    ( v1_xboole_0(sK15)
    | ~ spl28_12 ),
    inference(avatar_component_clause,[],[f445])).

fof(f659,plain,
    ( ~ spl28_73
    | spl28_63 ),
    inference(avatar_split_clause,[],[f652,f620,f657])).

fof(f652,plain,
    ( ~ v1_xboole_0(sK26)
    | ~ spl28_63 ),
    inference(resolution,[],[f398,f621])).

fof(f398,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f397,f292])).

fof(f397,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f337,f291])).

fof(f337,plain,(
    ! [X0] :
      ( v3_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f178])).

fof(f178,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f177])).

fof(f177,plain,(
    ! [X0] :
      ( ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',cc4_funct_1)).

fof(f650,plain,(
    spl28_70 ),
    inference(avatar_split_clause,[],[f254,f648])).

fof(f254,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f198])).

fof(f643,plain,(
    spl28_68 ),
    inference(avatar_split_clause,[],[f258,f641])).

fof(f641,plain,
    ( spl28_68
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_68])])).

fof(f636,plain,(
    spl28_66 ),
    inference(avatar_split_clause,[],[f383,f634])).

fof(f383,plain,(
    v1_funct_1(sK27) ),
    inference(cnf_transformation,[],[f250])).

fof(f250,plain,
    ( v1_funct_1(sK27)
    & v1_relat_1(sK27) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK27])],[f98,f249])).

fof(f249,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK27)
      & v1_relat_1(sK27) ) ),
    introduced(choice_axiom,[])).

fof(f98,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ? [X0] :
      ( v2_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_funct_1)).

fof(f629,plain,(
    spl28_64 ),
    inference(avatar_split_clause,[],[f382,f627])).

fof(f382,plain,(
    v1_relat_1(sK27) ),
    inference(cnf_transformation,[],[f250])).

fof(f622,plain,(
    ~ spl28_63 ),
    inference(avatar_split_clause,[],[f381,f620])).

fof(f381,plain,(
    ~ v3_funct_1(sK26) ),
    inference(cnf_transformation,[],[f248])).

fof(f248,plain,
    ( ~ v3_funct_1(sK26)
    & v1_funct_1(sK26)
    & v1_relat_1(sK26) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK26])],[f9,f247])).

fof(f247,plain,
    ( ? [X0] :
        ( ~ v3_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v3_funct_1(sK26)
      & v1_funct_1(sK26)
      & v1_relat_1(sK26) ) ),
    introduced(choice_axiom,[])).

fof(f9,axiom,(
    ? [X0] :
      ( ~ v3_funct_1(X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc5_funct_1)).

fof(f615,plain,(
    spl28_60 ),
    inference(avatar_split_clause,[],[f380,f613])).

fof(f380,plain,(
    v1_funct_1(sK26) ),
    inference(cnf_transformation,[],[f248])).

fof(f608,plain,(
    spl28_58 ),
    inference(avatar_split_clause,[],[f379,f606])).

fof(f379,plain,(
    v1_relat_1(sK26) ),
    inference(cnf_transformation,[],[f248])).

fof(f601,plain,(
    spl28_56 ),
    inference(avatar_split_clause,[],[f378,f599])).

fof(f378,plain,(
    v1_funct_1(sK25) ),
    inference(cnf_transformation,[],[f246])).

fof(f246,plain,
    ( v1_funct_1(sK25)
    & v1_relat_1(sK25) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25])],[f24,f245])).

fof(f245,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK25)
      & v1_relat_1(sK25) ) ),
    introduced(choice_axiom,[])).

fof(f24,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_funct_1)).

fof(f594,plain,(
    spl28_54 ),
    inference(avatar_split_clause,[],[f377,f592])).

fof(f377,plain,(
    v1_relat_1(sK25) ),
    inference(cnf_transformation,[],[f246])).

fof(f587,plain,(
    spl28_52 ),
    inference(avatar_split_clause,[],[f376,f585])).

fof(f376,plain,(
    v1_funct_1(sK24) ),
    inference(cnf_transformation,[],[f244])).

fof(f244,plain,
    ( v1_funct_1(sK24)
    & v1_relat_1(sK24) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK24])],[f97,f243])).

fof(f243,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( v1_funct_1(sK24)
      & v1_relat_1(sK24) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc3_funct_1)).

fof(f580,plain,(
    spl28_50 ),
    inference(avatar_split_clause,[],[f375,f578])).

fof(f375,plain,(
    v1_relat_1(sK24) ),
    inference(cnf_transformation,[],[f244])).

fof(f573,plain,(
    spl28_48 ),
    inference(avatar_split_clause,[],[f374,f571])).

fof(f374,plain,(
    v1_relat_1(sK23) ),
    inference(cnf_transformation,[],[f242])).

fof(f242,plain,(
    v1_relat_1(sK23) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23])],[f94,f241])).

fof(f241,plain,
    ( ? [X0] : v1_relat_1(X0)
   => v1_relat_1(sK23) ),
    introduced(choice_axiom,[])).

fof(f94,plain,(
    ? [X0] : v1_relat_1(X0) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ? [X0] :
      ( v2_relat_1(X0)
      & v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_relat_1)).

fof(f566,plain,(
    spl28_46 ),
    inference(avatar_split_clause,[],[f373,f564])).

fof(f564,plain,
    ( spl28_46
  <=> v7_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_46])])).

fof(f373,plain,(
    v7_struct_0(sK22) ),
    inference(cnf_transformation,[],[f240])).

fof(f240,plain,
    ( v7_struct_0(sK22)
    & ~ v2_struct_0(sK22)
    & l1_struct_0(sK22) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f92,f239])).

fof(f239,plain,
    ( ? [X0] :
        ( v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( v7_struct_0(sK22)
      & ~ v2_struct_0(sK22)
      & l1_struct_0(sK22) ) ),
    introduced(choice_axiom,[])).

fof(f92,axiom,(
    ? [X0] :
      ( v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc9_struct_0)).

fof(f559,plain,(
    ~ spl28_45 ),
    inference(avatar_split_clause,[],[f372,f557])).

fof(f557,plain,
    ( spl28_45
  <=> ~ v2_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_45])])).

fof(f372,plain,(
    ~ v2_struct_0(sK22) ),
    inference(cnf_transformation,[],[f240])).

fof(f552,plain,(
    spl28_42 ),
    inference(avatar_split_clause,[],[f371,f550])).

fof(f550,plain,
    ( spl28_42
  <=> l1_struct_0(sK22) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_42])])).

fof(f371,plain,(
    l1_struct_0(sK22) ),
    inference(cnf_transformation,[],[f240])).

fof(f545,plain,(
    ~ spl28_41 ),
    inference(avatar_split_clause,[],[f370,f543])).

fof(f543,plain,
    ( spl28_41
  <=> ~ v7_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_41])])).

fof(f370,plain,(
    ~ v7_struct_0(sK21) ),
    inference(cnf_transformation,[],[f238])).

fof(f238,plain,
    ( ~ v7_struct_0(sK21)
    & ~ v2_struct_0(sK21)
    & l1_struct_0(sK21) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f91,f237])).

fof(f237,plain,
    ( ? [X0] :
        ( ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0)
        & l1_struct_0(X0) )
   => ( ~ v7_struct_0(sK21)
      & ~ v2_struct_0(sK21)
      & l1_struct_0(sK21) ) ),
    introduced(choice_axiom,[])).

fof(f91,axiom,(
    ? [X0] :
      ( ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0)
      & l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc10_struct_0)).

fof(f538,plain,(
    ~ spl28_39 ),
    inference(avatar_split_clause,[],[f369,f536])).

fof(f536,plain,
    ( spl28_39
  <=> ~ v2_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_39])])).

fof(f369,plain,(
    ~ v2_struct_0(sK21) ),
    inference(cnf_transformation,[],[f238])).

fof(f531,plain,(
    spl28_36 ),
    inference(avatar_split_clause,[],[f368,f529])).

fof(f529,plain,
    ( spl28_36
  <=> l1_struct_0(sK21) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_36])])).

fof(f368,plain,(
    l1_struct_0(sK21) ),
    inference(cnf_transformation,[],[f238])).

fof(f524,plain,(
    spl28_34 ),
    inference(avatar_split_clause,[],[f367,f522])).

fof(f367,plain,(
    v1_zfmisc_1(sK20) ),
    inference(cnf_transformation,[],[f236])).

fof(f236,plain,
    ( v1_zfmisc_1(sK20)
    & ~ v1_xboole_0(sK20) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f57,f235])).

fof(f235,plain,
    ( ? [X0] :
        ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_zfmisc_1(sK20)
      & ~ v1_xboole_0(sK20) ) ),
    introduced(choice_axiom,[])).

fof(f57,axiom,(
    ? [X0] :
      ( v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_realset1)).

fof(f517,plain,(
    ~ spl28_33 ),
    inference(avatar_split_clause,[],[f366,f515])).

fof(f366,plain,(
    ~ v1_xboole_0(sK20) ),
    inference(cnf_transformation,[],[f236])).

fof(f510,plain,(
    spl28_30 ),
    inference(avatar_split_clause,[],[f365,f508])).

fof(f365,plain,(
    v1_funct_1(sK19) ),
    inference(cnf_transformation,[],[f234])).

fof(f234,plain,
    ( v1_funct_1(sK19)
    & v1_relat_1(sK19)
    & ~ v1_xboole_0(sK19) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f95,f233])).

fof(f233,plain,
    ( ? [X0] :
        ( v1_funct_1(X0)
        & v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_funct_1(sK19)
      & v1_relat_1(sK19)
      & ~ v1_xboole_0(sK19) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ? [X0] :
      ( v1_funct_1(X0)
      & v2_relat_1(X0)
      & v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc4_funct_1)).

fof(f503,plain,(
    spl28_28 ),
    inference(avatar_split_clause,[],[f364,f501])).

fof(f364,plain,(
    v1_relat_1(sK19) ),
    inference(cnf_transformation,[],[f234])).

fof(f496,plain,(
    ~ spl28_27 ),
    inference(avatar_split_clause,[],[f363,f494])).

fof(f363,plain,(
    ~ v1_xboole_0(sK19) ),
    inference(cnf_transformation,[],[f234])).

fof(f489,plain,(
    spl28_24 ),
    inference(avatar_split_clause,[],[f362,f487])).

fof(f362,plain,(
    v1_relat_1(sK18) ),
    inference(cnf_transformation,[],[f232])).

fof(f232,plain,
    ( v1_relat_1(sK18)
    & ~ v1_xboole_0(sK18) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f25,f231])).

fof(f231,plain,
    ( ? [X0] :
        ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v1_relat_1(sK18)
      & ~ v1_xboole_0(sK18) ) ),
    introduced(choice_axiom,[])).

fof(f25,axiom,(
    ? [X0] :
      ( v1_relat_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_relat_1)).

fof(f482,plain,(
    ~ spl28_23 ),
    inference(avatar_split_clause,[],[f361,f480])).

fof(f361,plain,(
    ~ v1_xboole_0(sK18) ),
    inference(cnf_transformation,[],[f232])).

fof(f475,plain,(
    spl28_20 ),
    inference(avatar_split_clause,[],[f360,f473])).

fof(f360,plain,(
    v4_funct_1(sK17) ),
    inference(cnf_transformation,[],[f230])).

fof(f230,plain,
    ( v4_funct_1(sK17)
    & ~ v1_xboole_0(sK17) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f26,f229])).

fof(f229,plain,
    ( ? [X0] :
        ( v4_funct_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( v4_funct_1(sK17)
      & ~ v1_xboole_0(sK17) ) ),
    introduced(choice_axiom,[])).

fof(f26,axiom,(
    ? [X0] :
      ( v4_funct_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc7_funct_1)).

fof(f468,plain,(
    ~ spl28_19 ),
    inference(avatar_split_clause,[],[f359,f466])).

fof(f359,plain,(
    ~ v1_xboole_0(sK17) ),
    inference(cnf_transformation,[],[f230])).

fof(f461,plain,(
    ~ spl28_17 ),
    inference(avatar_split_clause,[],[f358,f459])).

fof(f459,plain,
    ( spl28_17
  <=> ~ v1_zfmisc_1(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_17])])).

fof(f358,plain,(
    ~ v1_zfmisc_1(sK16) ),
    inference(cnf_transformation,[],[f228])).

fof(f228,plain,
    ( ~ v1_zfmisc_1(sK16)
    & ~ v1_xboole_0(sK16) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f62,f227])).

fof(f227,plain,
    ( ? [X0] :
        ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
   => ( ~ v1_zfmisc_1(sK16)
      & ~ v1_xboole_0(sK16) ) ),
    introduced(choice_axiom,[])).

fof(f62,axiom,(
    ? [X0] :
      ( ~ v1_zfmisc_1(X0)
      & ~ v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_realset1)).

fof(f454,plain,(
    ~ spl28_15 ),
    inference(avatar_split_clause,[],[f357,f452])).

fof(f452,plain,
    ( spl28_15
  <=> ~ v1_xboole_0(sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_15])])).

fof(f357,plain,(
    ~ v1_xboole_0(sK16) ),
    inference(cnf_transformation,[],[f228])).

fof(f447,plain,(
    spl28_12 ),
    inference(avatar_split_clause,[],[f356,f445])).

fof(f356,plain,(
    v1_xboole_0(sK15) ),
    inference(cnf_transformation,[],[f226])).

fof(f226,plain,(
    v1_xboole_0(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f60,f225])).

fof(f225,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK15) ),
    introduced(choice_axiom,[])).

fof(f60,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc1_xboole_0)).

fof(f440,plain,(
    spl28_10 ),
    inference(avatar_split_clause,[],[f355,f438])).

fof(f438,plain,
    ( spl28_10
  <=> l1_struct_0(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_10])])).

fof(f355,plain,(
    l1_struct_0(sK14) ),
    inference(cnf_transformation,[],[f224])).

fof(f224,plain,(
    l1_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f76,f223])).

fof(f223,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK14) ),
    introduced(choice_axiom,[])).

fof(f76,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',existence_l1_struct_0)).

fof(f433,plain,(
    ~ spl28_9 ),
    inference(avatar_split_clause,[],[f354,f431])).

fof(f431,plain,
    ( spl28_9
  <=> ~ v1_xboole_0(sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl28_9])])).

fof(f354,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(cnf_transformation,[],[f222])).

fof(f222,plain,(
    ~ v1_xboole_0(sK13) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f65,f221])).

fof(f221,plain,
    ( ? [X0] : ~ v1_xboole_0(X0)
   => ~ v1_xboole_0(sK13) ),
    introduced(choice_axiom,[])).

fof(f65,axiom,(
    ? [X0] : ~ v1_xboole_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',rc2_xboole_0)).

fof(f426,plain,(
    spl28_6 ),
    inference(avatar_split_clause,[],[f256,f424])).

fof(f256,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t9_tex_2.p',dt_o_0_0_xboole_0)).

fof(f419,plain,(
    spl28_4 ),
    inference(avatar_split_clause,[],[f253,f417])).

fof(f253,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f198])).

fof(f412,plain,(
    ~ spl28_3 ),
    inference(avatar_split_clause,[],[f252,f410])).

fof(f252,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f198])).

fof(f405,plain,(
    ~ spl28_1 ),
    inference(avatar_split_clause,[],[f251,f403])).

fof(f251,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f198])).
%------------------------------------------------------------------------------
