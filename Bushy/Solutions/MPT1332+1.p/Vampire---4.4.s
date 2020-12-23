%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_2__t55_tops_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:40 EDT 2019

% Result     : Theorem 90.96s
% Output     : Refutation 90.96s
% Verified   : 
% Statistics : Number of formulae       : 1850 (13896 expanded)
%              Number of leaves         :  414 (4844 expanded)
%              Depth                    :   17
%              Number of atoms          : 4715 (29016 expanded)
%              Number of equality atoms :  236 (5469 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62232,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f162,f169,f176,f183,f190,f203,f210,f217,f224,f239,f255,f262,f269,f276,f297,f310,f320,f327,f337,f371,f395,f396,f405,f417,f435,f451,f458,f481,f502,f602,f611,f627,f951,f1078,f1092,f2121,f2128,f2145,f2161,f2168,f2601,f2608,f3386,f4199,f4209,f4283,f4299,f4307,f4385,f4408,f4424,f4481,f4614,f4630,f4920,f4983,f5201,f5681,f5886,f6020,f6073,f6154,f6161,f6199,f6206,f6223,f6264,f6281,f6513,f6520,f6710,f7192,f10523,f10819,f11380,f11387,f12070,f12084,f14067,f14382,f16184,f16191,f16210,f17748,f17762,f17769,f17776,f18029,f18036,f18043,f18932,f19155,f20547,f20576,f20615,f20632,f20693,f22200,f22204,f22217,f22224,f22233,f22264,f22316,f22325,f22355,f22395,f22404,f22420,f24529,f24533,f24753,f24760,f24777,f25143,f25147,f25162,f25185,f25201,f25232,f25241,f25257,f25264,f25318,f25325,f25342,f25351,f25367,f25374,f25381,f25452,f25459,f25491,f25498,f25505,f25548,f25569,f25576,f25588,f25604,f25611,f25620,f25631,f25638,f25651,f25653,f25938,f25990,f25997,f26054,f26099,f26791,f26798,f26832,f26839,f26909,f26978,f26985,f27006,f27013,f27086,f27093,f27110,f27117,f27124,f27275,f27282,f27289,f27306,f27320,f27327,f27334,f27600,f27706,f27790,f27797,f27804,f27823,f27837,f27844,f27851,f27915,f27945,f28062,f28074,f28103,f28119,f28126,f28145,f28152,f28186,f28193,f28218,f28571,f28578,f28589,f28736,f28739,f28747,f28750,f28776,f28779,f28781,f28783,f28785,f28787,f28790,f28792,f28810,f28994,f28996,f29011,f29018,f29231,f29259,f29319,f29326,f29398,f29446,f29554,f29591,f29655,f29743,f29748,f29763,f29766,f29787,f29820,f29849,f32552,f32561,f32572,f32579,f32595,f32785,f32792,f32810,f32843,f32854,f32882,f32899,f32906,f33269,f33276,f33619,f36430,f36446,f36453,f36460,f36528,f36545,f36552,f36751,f36758,f37069,f37071,f37073,f37075,f37077,f37079,f37262,f37264,f37279,f37293,f37356,f37379,f37429,f37436,f37443,f37505,f37512,f37526,f37560,f37588,f37602,f37641,f37648,f37650,f37652,f37655,f37662,f37669,f37677,f37685,f37736,f37925,f38025,f38027,f38028,f38031,f38036,f38060,f38079,f38123,f38254,f38285,f38306,f38320,f38341,f38362,f38435,f38451,f38543,f38583,f38592,f38605,f38613,f38742,f38764,f38772,f39006,f39061,f39116,f39148,f39180,f39361,f39455,f39478,f39501,f39587,f39617,f39624,f39726,f39733,f39740,f39743,f39745,f39747,f39749,f39751,f39753,f39755,f39756,f39758,f39857,f39864,f39871,f39924,f39940,f39954,f39961,f39968,f39975,f39993,f40000,f40007,f40045,f40110,f40117,f40139,f40148,f43270,f43271,f43822,f43829,f43840,f43852,f43859,f43871,f43887,f43907,f43914,f44291,f44300,f44316,f44367,f44375,f44576,f44740,f44992,f45023,f45340,f45347,f45760,f45769,f45864,f45898,f45911,f45913,f46024,f46274,f46832,f46910,f51087,f55596,f55850,f55852,f58432,f58506])).

fof(f58506,plain,
    ( ~ spl10_26
    | ~ spl10_32
    | ~ spl10_208
    | ~ spl10_212
    | ~ spl10_220
    | spl10_625 ),
    inference(avatar_contradiction_clause,[],[f58505])).

fof(f58505,plain,
    ( $false
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_208
    | ~ spl10_212
    | ~ spl10_220
    | ~ spl10_625 ),
    inference(subsumption_resolution,[],[f58490,f43821])).

fof(f43821,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_625 ),
    inference(avatar_component_clause,[],[f43820])).

fof(f43820,plain,
    ( spl10_625
  <=> ~ v4_pre_topc(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_625])])).

fof(f58490,plain,
    ( v4_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_208
    | ~ spl10_212
    | ~ spl10_220 ),
    inference(backward_demodulation,[],[f58489,f22216])).

fof(f22216,plain,
    ( v4_pre_topc(sK6(sK2,sK4,sK3),sK3)
    | ~ spl10_208 ),
    inference(avatar_component_clause,[],[f22215])).

fof(f22215,plain,
    ( spl10_208
  <=> v4_pre_topc(sK6(sK2,sK4,sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_208])])).

fof(f58489,plain,
    ( k1_xboole_0 = sK6(sK2,sK4,sK3)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212
    | ~ spl10_220 ),
    inference(forward_demodulation,[],[f56076,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0) ),
    inference(definition_unfolding,[],[f111,f131])).

fof(f131,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',redefinition_k6_subset_1)).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t4_boole)).

fof(f56076,plain,
    ( k6_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,sK6(sK2,sK4,sK3))) = sK6(sK2,sK4,sK3)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212
    | ~ spl10_220 ),
    inference(backward_demodulation,[],[f380,f22377])).

fof(f22377,plain,
    ( k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))) = sK6(sK2,sK4,sK3)
    | ~ spl10_212
    | ~ spl10_220 ),
    inference(forward_demodulation,[],[f22362,f22236])).

fof(f22236,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))) = sK6(sK2,sK4,sK3)
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22232,f136])).

fof(f136,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',involutiveness_k3_subset_1)).

fof(f22232,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(avatar_component_clause,[],[f22231])).

fof(f22231,plain,
    ( spl10_212
  <=> m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_212])])).

fof(f22362,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))) = k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)))
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f22354,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f137,f131])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',d5_subset_1)).

fof(f22354,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_220 ),
    inference(avatar_component_clause,[],[f22353])).

fof(f22353,plain,
    ( spl10_220
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_220])])).

fof(f380,plain,
    ( u1_struct_0(sK3) = k1_xboole_0
    | ~ spl10_26
    | ~ spl10_32 ),
    inference(backward_demodulation,[],[f300,f268])).

fof(f268,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl10_26
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f300,plain,
    ( k2_struct_0(sK3) = k1_xboole_0
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl10_32
  <=> k2_struct_0(sK3) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f58432,plain,
    ( ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212
    | ~ spl10_214
    | spl10_627 ),
    inference(avatar_contradiction_clause,[],[f58431])).

fof(f58431,plain,
    ( $false
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212
    | ~ spl10_214
    | ~ spl10_627 ),
    inference(subsumption_resolution,[],[f58430,f43828])).

fof(f43828,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_627 ),
    inference(avatar_component_clause,[],[f43827])).

fof(f43827,plain,
    ( spl10_627
  <=> ~ v3_pre_topc(k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_627])])).

fof(f58430,plain,
    ( v3_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212
    | ~ spl10_214 ),
    inference(forward_demodulation,[],[f56043,f58429])).

fof(f58429,plain,
    ( k1_xboole_0 = k3_subset_1(k1_xboole_0,sK6(sK2,sK4,sK3))
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212 ),
    inference(forward_demodulation,[],[f56038,f153])).

fof(f56038,plain,
    ( k3_subset_1(k1_xboole_0,sK6(sK2,sK4,sK3)) = k6_subset_1(k1_xboole_0,sK6(sK2,sK4,sK3))
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_212 ),
    inference(backward_demodulation,[],[f380,f22239])).

fof(f22239,plain,
    ( k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)) = k6_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22232,f154])).

fof(f56043,plain,
    ( v3_pre_topc(k3_subset_1(k1_xboole_0,sK6(sK2,sK4,sK3)),sK3)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_214 ),
    inference(backward_demodulation,[],[f380,f22263])).

fof(f22263,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),sK3)
    | ~ spl10_214 ),
    inference(avatar_component_clause,[],[f22262])).

fof(f22262,plain,
    ( spl10_214
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_214])])).

fof(f55852,plain,
    ( ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | spl10_401 ),
    inference(avatar_contradiction_clause,[],[f55851])).

fof(f55851,plain,
    ( $false
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_401 ),
    inference(subsumption_resolution,[],[f49392,f49471])).

fof(f49471,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(sK4,X0)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70 ),
    inference(forward_demodulation,[],[f49469,f950])).

fof(f950,plain,
    ( k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0)
    | ~ spl10_70 ),
    inference(avatar_component_clause,[],[f949])).

fof(f949,plain,
    ( spl10_70
  <=> k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_70])])).

fof(f49469,plain,
    ( ! [X0] : k3_subset_1(k1_xboole_0,k1_xboole_0) = k10_relat_1(sK4,X0)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(backward_demodulation,[],[f49468,f47244])).

fof(f47244,plain,
    ( ! [X0] : k3_subset_1(k1_xboole_0,k3_subset_1(k1_xboole_0,k10_relat_1(sK4,X0))) = k10_relat_1(sK4,X0)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(backward_demodulation,[],[f47188,f3737])).

fof(f3737,plain,
    ( ! [X0] : k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0))) = k10_relat_1(sK4,X0)
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f3321])).

fof(f3321,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1935,f136])).

fof(f1935,plain,
    ( ! [X0] : m1_subset_1(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',dt_k8_relset_1)).

fof(f296,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_30
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_30])])).

fof(f3662,plain,
    ( ! [X0] : k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0)
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f149])).

fof(f149,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',redefinition_k8_relset_1)).

fof(f47188,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | ~ spl10_24
    | ~ spl10_46 ),
    inference(backward_demodulation,[],[f404,f261])).

fof(f261,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl10_24
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f404,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f403])).

fof(f403,plain,
    ( spl10_46
  <=> k2_struct_0(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f49468,plain,
    ( ! [X0] : k1_xboole_0 = k3_subset_1(k1_xboole_0,k10_relat_1(sK4,X0))
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(forward_demodulation,[],[f47246,f153])).

fof(f47246,plain,
    ( ! [X0] : k3_subset_1(k1_xboole_0,k10_relat_1(sK4,X0)) = k6_subset_1(k1_xboole_0,k10_relat_1(sK4,X0))
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(backward_demodulation,[],[f47188,f3739])).

fof(f3739,plain,
    ( ! [X0] : k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0)) = k6_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0))
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f3324])).

fof(f3324,plain,
    ( ! [X0] : k3_subset_1(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)) = k6_subset_1(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1935,f154])).

fof(f49392,plain,
    ( k1_xboole_0 != k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_24
    | ~ spl10_46
    | ~ spl10_401 ),
    inference(backward_demodulation,[],[f47188,f29014])).

fof(f29014,plain,
    ( u1_struct_0(sK2) != k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_401 ),
    inference(avatar_component_clause,[],[f29013])).

fof(f29013,plain,
    ( spl10_401
  <=> u1_struct_0(sK2) != k10_relat_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_401])])).

fof(f55850,plain,
    ( ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | spl10_397 ),
    inference(avatar_contradiction_clause,[],[f55849])).

fof(f55849,plain,
    ( $false
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_397 ),
    inference(subsumption_resolution,[],[f49391,f50086])).

fof(f50086,plain,
    ( ! [X0] : k1_xboole_0 = k8_relset_1(k1_xboole_0,u1_struct_0(sK3),sK4,X0)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70 ),
    inference(backward_demodulation,[],[f49471,f47239])).

fof(f47239,plain,
    ( ! [X0] : k8_relset_1(k1_xboole_0,u1_struct_0(sK3),sK4,X0) = k10_relat_1(sK4,X0)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46 ),
    inference(backward_demodulation,[],[f47188,f3662])).

fof(f49391,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,u1_struct_0(sK3),sK4,u1_struct_0(sK3))
    | ~ spl10_24
    | ~ spl10_46
    | ~ spl10_397 ),
    inference(backward_demodulation,[],[f47188,f28585])).

fof(f28585,plain,
    ( u1_struct_0(sK2) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3))
    | ~ spl10_397 ),
    inference(avatar_component_clause,[],[f28584])).

fof(f28584,plain,
    ( spl10_397
  <=> u1_struct_0(sK2) != k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_397])])).

fof(f55596,plain,
    ( ~ spl10_0
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224
    | spl10_633 ),
    inference(avatar_contradiction_clause,[],[f55595])).

fof(f55595,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224
    | ~ spl10_633 ),
    inference(subsumption_resolution,[],[f55594,f50125])).

fof(f50125,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK2)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_633 ),
    inference(backward_demodulation,[],[f49471,f43858])).

fof(f43858,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2)
    | ~ spl10_633 ),
    inference(avatar_component_clause,[],[f43857])).

fof(f43857,plain,
    ( spl10_633
  <=> ~ v4_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_633])])).

fof(f55594,plain,
    ( v4_pre_topc(k1_xboole_0,sK2)
    | ~ spl10_0
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224 ),
    inference(forward_demodulation,[],[f55593,f950])).

fof(f55593,plain,
    ( v4_pre_topc(k3_subset_1(k1_xboole_0,k1_xboole_0),sK2)
    | ~ spl10_0
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224 ),
    inference(forward_demodulation,[],[f49313,f49471])).

fof(f49313,plain,
    ( v4_pre_topc(k3_subset_1(k1_xboole_0,k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)))),sK2)
    | ~ spl10_0
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_224 ),
    inference(backward_demodulation,[],[f47188,f22406])).

fof(f22406,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)))),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_224 ),
    inference(unit_resulting_resolution,[],[f161,f3735,f22403,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f91,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t30_tops_1)).

fof(f22403,plain,
    ( v3_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))),sK2)
    | ~ spl10_224 ),
    inference(avatar_component_clause,[],[f22402])).

fof(f22402,plain,
    ( spl10_224
  <=> v3_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_224])])).

fof(f3735,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK4,X0),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f1935])).

fof(f161,plain,
    ( l1_pre_topc(sK2)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl10_0
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f51087,plain,
    ( ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224
    | spl10_631 ),
    inference(avatar_contradiction_clause,[],[f51086])).

fof(f51086,plain,
    ( $false
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224
    | ~ spl10_631 ),
    inference(subsumption_resolution,[],[f50145,f50124])).

fof(f50124,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK2)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_631 ),
    inference(backward_demodulation,[],[f49471,f43851])).

fof(f43851,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2)
    | ~ spl10_631 ),
    inference(avatar_component_clause,[],[f43850])).

fof(f43850,plain,
    ( spl10_631
  <=> ~ v3_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_631])])).

fof(f50145,plain,
    ( v3_pre_topc(k1_xboole_0,sK2)
    | ~ spl10_24
    | ~ spl10_30
    | ~ spl10_46
    | ~ spl10_70
    | ~ spl10_224 ),
    inference(backward_demodulation,[],[f49471,f22403])).

fof(f46910,plain,
    ( ~ spl10_4
    | spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | spl10_167
    | ~ spl10_212
    | ~ spl10_214
    | ~ spl10_400 ),
    inference(avatar_contradiction_clause,[],[f46909])).

fof(f46909,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_167
    | ~ spl10_212
    | ~ spl10_214
    | ~ spl10_400 ),
    inference(subsumption_resolution,[],[f46908,f22263])).

fof(f46908,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),sK3)
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_167
    | ~ spl10_212
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f46900,f22239])).

fof(f46900,plain,
    ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),sK3)
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_167
    | ~ spl10_400 ),
    inference(unit_resulting_resolution,[],[f14066,f29218])).

fof(f29218,plain,
    ( ! [X9] :
        ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK3),X9),sK3)
        | v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X9)),sK2) )
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(backward_demodulation,[],[f29217,f5156])).

fof(f5156,plain,
    ( ! [X9] :
        ( ~ v3_pre_topc(k6_subset_1(u1_struct_0(sK3),X9),sK3)
        | v3_pre_topc(k10_relat_1(sK4,k6_subset_1(u1_struct_0(sK3),X9)),sK2) )
    | ~ spl10_19
    | ~ spl10_30 ),
    inference(resolution,[],[f3734,f130])).

fof(f130,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',dt_k6_subset_1)).

fof(f3734,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X4,sK3)
        | v3_pre_topc(k10_relat_1(sK4,X4),sK2) )
    | ~ spl10_19
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f406])).

fof(f406,plain,
    ( ! [X4] :
        ( v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4),sK2)
        | ~ v3_pre_topc(X4,sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl10_19 ),
    inference(subsumption_resolution,[],[f106,f232])).

fof(f232,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl10_19
  <=> ~ v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f106,plain,(
    ! [X4] :
      ( v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4),sK2)
      | ~ v3_pre_topc(X4,sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,
    ( ( ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),sK2)
        & v3_pre_topc(sK5,sK3)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) )
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( ! [X4] :
          ( v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X4),sK2)
          | ~ v3_pre_topc(X4,sK3)
          | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
      | v5_pre_topc(sK4,sK2,sK3) )
    & ( k2_struct_0(sK2) = k1_xboole_0
      | k2_struct_0(sK3) != k1_xboole_0 )
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & l1_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f79,f83,f82,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ? [X3] :
                      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v3_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) )
                & ( ! [X4] :
                      ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v3_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | v5_pre_topc(X2,X0,X1) )
                & ( k2_struct_0(X0) = k1_xboole_0
                  | k2_struct_0(X1) != k1_xboole_0 )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X3),sK2)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,sK2,X1) )
              & ( ! [X4] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2,X4),sK2)
                    | ~ v3_pre_topc(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,sK2,X1) )
              & ( k2_struct_0(sK2) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                    | ~ v3_pre_topc(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
     => ( ? [X2] :
            ( ( ? [X3] :
                  ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X3),X0)
                  & v3_pre_topc(X3,sK3)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK3))) )
              | ~ v5_pre_topc(X2,X0,sK3) )
            & ( ! [X4] :
                  ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2,X4),X0)
                  | ~ v3_pre_topc(X4,sK3)
                  | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3))) )
              | v5_pre_topc(X2,X0,sK3) )
            & ( k2_struct_0(X0) = k1_xboole_0
              | k2_struct_0(sK3) != k1_xboole_0 )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_pre_topc(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ? [X3] :
                ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                & v3_pre_topc(X3,X1)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            | ~ v5_pre_topc(X2,X0,X1) )
          & ( ! [X4] :
                ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                | ~ v3_pre_topc(X4,X1)
                | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
            | v5_pre_topc(X2,X0,X1) )
          & ( k2_struct_0(X0) = k1_xboole_0
            | k2_struct_0(X1) != k1_xboole_0 )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( ? [X3] :
              ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X3),X0)
              & v3_pre_topc(X3,X1)
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ v5_pre_topc(sK4,X0,X1) )
        & ( ! [X4] :
              ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4,X4),X0)
              | ~ v3_pre_topc(X4,X1)
              | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
          | v5_pre_topc(sK4,X0,X1) )
        & ( k2_struct_0(X0) = k1_xboole_0
          | k2_struct_0(X1) != k1_xboole_0 )
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v3_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5),X0)
        & v3_pre_topc(sK5,X1)
        & m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X4] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                    | ~ v3_pre_topc(X4,X1)
                    | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ? [X3] :
                    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    & v3_pre_topc(X3,X1)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | ~ v5_pre_topc(X2,X0,X1) )
              & ( ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                | v5_pre_topc(X2,X0,X1) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <~> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              & ( k2_struct_0(X0) = k1_xboole_0
                | k2_struct_0(X1) != k1_xboole_0 )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k2_struct_0(X1) = k1_xboole_0
                   => k2_struct_0(X0) = k1_xboole_0 )
                 => ( v5_pre_topc(X2,X0,X1)
                  <=> ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                       => ( v3_pre_topc(X3,X1)
                         => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t55_tops_2)).

fof(f29217,plain,
    ( ! [X96] : k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X96)) = k10_relat_1(sK4,k6_subset_1(u1_struct_0(sK3),X96))
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f29122,f3739])).

fof(f29122,plain,
    ( ! [X96] : k6_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X96)) = k10_relat_1(sK4,k6_subset_1(u1_struct_0(sK3),X96))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(superposition,[],[f16903,f29017])).

fof(f29017,plain,
    ( u1_struct_0(sK2) = k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_400 ),
    inference(avatar_component_clause,[],[f29016])).

fof(f29016,plain,
    ( spl10_400
  <=> u1_struct_0(sK2) = k10_relat_1(sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_400])])).

fof(f16903,plain,
    ( ! [X0,X1] : k6_subset_1(k10_relat_1(sK4,X0),k10_relat_1(sK4,X1)) = k10_relat_1(sK4,k6_subset_1(X0,X1))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f480,f175,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k6_subset_1(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) = k10_relat_1(X2,k6_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t138_funct_1)).

fof(f175,plain,
    ( v1_funct_1(sK4)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f174])).

fof(f174,plain,
    ( spl10_4
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f480,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f479])).

fof(f479,plain,
    ( spl10_56
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f14066,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK6(sK2,sK4,sK3))),sK2)
    | ~ spl10_167 ),
    inference(avatar_component_clause,[],[f14065])).

fof(f14065,plain,
    ( spl10_167
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK6(sK2,sK4,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_167])])).

fof(f46832,plain,
    ( spl10_680
    | spl10_229
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f29477,f25503,f22415,f46830])).

fof(f46830,plain,
    ( spl10_680
  <=> r2_hidden(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_680])])).

fof(f22415,plain,
    ( spl10_229
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_229])])).

fof(f25503,plain,
    ( spl10_274
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_274])])).

fof(f29477,plain,
    ( r2_hidden(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_274 ),
    inference(superposition,[],[f28794,f878])).

fof(f878,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k6_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f225,f154])).

fof(f225,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f130,f152])).

fof(f152,plain,(
    ! [X0] : k6_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f110,f131])).

fof(f110,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t3_boole)).

fof(f28794,plain,
    ( ! [X17] : r2_hidden(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X17),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_274 ),
    inference(subsumption_resolution,[],[f27234,f22416])).

fof(f22416,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(avatar_component_clause,[],[f22415])).

fof(f27234,plain,
    ( ! [X17] :
        ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
        | r2_hidden(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X17),k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl10_274 ),
    inference(resolution,[],[f25529,f134])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t2_subset)).

fof(f25529,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(forward_demodulation,[],[f25511,f25514])).

fof(f25514,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5),X0)
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25504,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k6_subset_1(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(definition_unfolding,[],[f143,f131])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',redefinition_k7_subset_1)).

fof(f25504,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(avatar_component_clause,[],[f25503])).

fof(f25511,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25504,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',dt_k7_subset_1)).

fof(f46274,plain,
    ( spl10_678
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(avatar_split_clause,[],[f46033,f29016,f479,f174,f46272])).

fof(f46272,plain,
    ( spl10_678
  <=> k6_subset_1(k10_relat_1(sK4,k1_xboole_0),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_678])])).

fof(f46033,plain,
    ( k6_subset_1(k10_relat_1(sK4,k1_xboole_0),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(superposition,[],[f29121,f153])).

fof(f29121,plain,
    ( ! [X95] : k6_subset_1(k10_relat_1(sK4,X95),u1_struct_0(sK2)) = k10_relat_1(sK4,k6_subset_1(X95,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(superposition,[],[f16903,f29017])).

fof(f46024,plain,
    ( ~ spl10_677
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28968,f25196,f46022])).

fof(f46022,plain,
    ( spl10_677
  <=> ~ r2_hidden(sK5,k3_subset_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_677])])).

fof(f25196,plain,
    ( spl10_241
  <=> ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_241])])).

fof(f28968,plain,
    ( ~ r2_hidden(sK5,k3_subset_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f2211])).

fof(f2211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k3_subset_1(sK7(k1_zfmisc_1(X0)),sK7(k1_zfmisc_1(X0))))
      | m1_subset_1(X1,X0) ) ),
    inference(superposition,[],[f1426,f878])).

fof(f1426,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k6_subset_1(sK7(k1_zfmisc_1(X6)),X7))
      | m1_subset_1(X5,X6) ) ),
    inference(backward_demodulation,[],[f1398,f798])).

fof(f798,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,k7_subset_1(X6,sK7(k1_zfmisc_1(X6)),X7))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f742,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t4_subset)).

fof(f742,plain,(
    ! [X0,X1] : m1_subset_1(k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f129,f142])).

fof(f129,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] : m1_subset_1(sK7(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK7(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f23,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',existence_m1_subset_1)).

fof(f1398,plain,(
    ! [X0,X1] : k6_subset_1(sK7(k1_zfmisc_1(X0)),X1) = k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1) ),
    inference(unit_resulting_resolution,[],[f129,f155])).

fof(f25197,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_241 ),
    inference(avatar_component_clause,[],[f25196])).

fof(f45913,plain,
    ( ~ spl10_673
    | ~ spl10_2
    | ~ spl10_262
    | spl10_675 ),
    inference(avatar_split_clause,[],[f45912,f45909,f25372,f167,f45900])).

fof(f45900,plain,
    ( spl10_673
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_673])])).

fof(f167,plain,
    ( spl10_2
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f25372,plain,
    ( spl10_262
  <=> m1_subset_1(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_262])])).

fof(f45909,plain,
    ( spl10_675
  <=> ~ v4_pre_topc(k3_subset_1(sK5,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_675])])).

fof(f45912,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3)
    | ~ spl10_2
    | ~ spl10_262
    | ~ spl10_675 ),
    inference(unit_resulting_resolution,[],[f168,f25373,f45910,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t29_tops_1)).

fof(f45910,plain,
    ( ~ v4_pre_topc(k3_subset_1(sK5,sK5),sK3)
    | ~ spl10_675 ),
    inference(avatar_component_clause,[],[f45909])).

fof(f25373,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(avatar_component_clause,[],[f25372])).

fof(f168,plain,
    ( l1_pre_topc(sK3)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f167])).

fof(f45911,plain,
    ( spl10_672
    | ~ spl10_675
    | ~ spl10_2
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f25403,f25372,f167,f45909,f45903])).

fof(f45903,plain,
    ( spl10_672
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_672])])).

fof(f25403,plain,
    ( ~ v4_pre_topc(k3_subset_1(sK5,sK5),sK3)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3)
    | ~ spl10_2
    | ~ spl10_262 ),
    inference(subsumption_resolution,[],[f25391,f168])).

fof(f25391,plain,
    ( ~ v4_pre_topc(k3_subset_1(sK5,sK5),sK3)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl10_262 ),
    inference(resolution,[],[f25373,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f45898,plain,
    ( spl10_670
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f25387,f25372,f45896])).

fof(f45896,plain,
    ( spl10_670
  <=> k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)) = k6_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_670])])).

fof(f25387,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)) = k6_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25373,f154])).

fof(f45864,plain,
    ( spl10_668
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f45854,f29552,f45862])).

fof(f45862,plain,
    ( spl10_668
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_668])])).

fof(f29552,plain,
    ( spl10_410
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_410])])).

fof(f45854,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))),u1_struct_0(sK3))
    | ~ spl10_410 ),
    inference(superposition,[],[f45819,f907])).

fof(f907,plain,(
    ! [X0] : k6_subset_1(X0,k3_subset_1(X0,sK7(k1_zfmisc_1(X0)))) = sK7(k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f882,f635])).

fof(f635,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,sK7(k1_zfmisc_1(X0)))) = sK7(k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f129,f136])).

fof(f882,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,sK7(k1_zfmisc_1(X0)))) = k6_subset_1(X0,k3_subset_1(X0,sK7(k1_zfmisc_1(X0)))) ),
    inference(unit_resulting_resolution,[],[f516,f154])).

fof(f516,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK7(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f129,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',dt_k3_subset_1)).

fof(f45819,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X0),u1_struct_0(sK3))
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f29577,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t3_subset)).

fof(f29577,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_410 ),
    inference(forward_demodulation,[],[f29559,f29562])).

fof(f29562,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X0)
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f29553,f155])).

fof(f29553,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_410 ),
    inference(avatar_component_clause,[],[f29552])).

fof(f29559,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f29553,f142])).

fof(f45769,plain,
    ( spl10_666
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f27235,f25503,f45767])).

fof(f45767,plain,
    ( spl10_666
  <=> m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_666])])).

fof(f27235,plain,
    ( m1_subset_1(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(superposition,[],[f25529,f878])).

fof(f45760,plain,
    ( spl10_664
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f45750,f25503,f45758])).

fof(f45758,plain,
    ( spl10_664
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_664])])).

fof(f45750,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5)))),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(superposition,[],[f45709,f907])).

fof(f45709,plain,
    ( ! [X0] : r1_tarski(k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0)),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f27226,f138])).

fof(f27226,plain,
    ( ! [X5] : m1_subset_1(k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(resolution,[],[f25529,f135])).

fof(f45347,plain,
    ( spl10_662
    | spl10_617 ),
    inference(avatar_split_clause,[],[f43845,f40128,f45345])).

fof(f45345,plain,
    ( spl10_662
  <=> r2_hidden(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),k3_subset_1(u1_struct_0(sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_662])])).

fof(f40128,plain,
    ( spl10_617
  <=> ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_617])])).

fof(f43845,plain,
    ( r2_hidden(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_617 ),
    inference(unit_resulting_resolution,[],[f129,f40129,f134])).

fof(f40129,plain,
    ( ~ v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_617 ),
    inference(avatar_component_clause,[],[f40128])).

fof(f45340,plain,
    ( ~ spl10_661
    | spl10_617 ),
    inference(avatar_split_clause,[],[f43843,f40128,f45338])).

fof(f45338,plain,
    ( spl10_661
  <=> ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK5),sK7(k3_subset_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_661])])).

fof(f43843,plain,
    ( ~ r2_hidden(k3_subset_1(u1_struct_0(sK3),sK5),sK7(k3_subset_1(u1_struct_0(sK3),sK5)))
    | ~ spl10_617 ),
    inference(unit_resulting_resolution,[],[f40129,f363])).

fof(f363,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK7(X1))
      | v1_xboole_0(X1) ) ),
    inference(resolution,[],[f360,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',antisymmetry_r2_hidden)).

fof(f360,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),X3)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f134,f129])).

fof(f45023,plain,
    ( spl10_658
    | ~ spl10_30
    | ~ spl10_656 ),
    inference(avatar_split_clause,[],[f44997,f44990,f295,f45021])).

fof(f45021,plain,
    ( spl10_658
  <=> k6_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_658])])).

fof(f44990,plain,
    ( spl10_656
  <=> u1_struct_0(sK2) = k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_656])])).

fof(f44997,plain,
    ( k6_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_30
    | ~ spl10_656 ),
    inference(superposition,[],[f4049,f44991])).

fof(f44991,plain,
    ( u1_struct_0(sK2) = k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k1_xboole_0))
    | ~ spl10_656 ),
    inference(avatar_component_clause,[],[f44990])).

fof(f4049,plain,
    ( ! [X0] : k6_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0))) = k10_relat_1(sK4,X0)
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f4038,f3737])).

fof(f4038,plain,
    ( ! [X0] : k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0))) = k6_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f3736,f154])).

fof(f3736,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f3320])).

fof(f3320,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(u1_struct_0(sK2),k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X0)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1935,f135])).

fof(f44992,plain,
    ( spl10_656
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_640 ),
    inference(avatar_split_clause,[],[f44267,f43912,f29016,f479,f174,f44990])).

fof(f43912,plain,
    ( spl10_640
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_640])])).

fof(f44267,plain,
    ( u1_struct_0(sK2) = k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_640 ),
    inference(forward_demodulation,[],[f44039,f29017])).

fof(f44039,plain,
    ( k3_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_640 ),
    inference(superposition,[],[f17385,f43913])).

fof(f43913,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ spl10_640 ),
    inference(avatar_component_clause,[],[f43912])).

fof(f17385,plain,
    ( ! [X0] : k3_subset_1(k10_relat_1(sK4,X0),k10_relat_1(sK4,k3_subset_1(X0,X0))) = k10_relat_1(sK4,X0)
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17384,f910])).

fof(f910,plain,(
    ! [X0] : k6_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f879,f628])).

fof(f628,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f225,f136])).

fof(f879,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = k6_subset_1(X0,k3_subset_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f513,f154])).

fof(f513,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f225,f135])).

fof(f17384,plain,
    ( ! [X0] : k3_subset_1(k10_relat_1(sK4,X0),k10_relat_1(sK4,k3_subset_1(X0,X0))) = k10_relat_1(sK4,k6_subset_1(X0,k3_subset_1(X0,X0)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17372,f16903])).

fof(f17372,plain,
    ( ! [X0] : k3_subset_1(k10_relat_1(sK4,X0),k10_relat_1(sK4,k3_subset_1(X0,X0))) = k6_subset_1(k10_relat_1(sK4,X0),k10_relat_1(sK4,k3_subset_1(X0,X0)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f17324,f154])).

fof(f17324,plain,
    ( ! [X0] : m1_subset_1(k10_relat_1(sK4,k3_subset_1(X0,X0)),k1_zfmisc_1(k10_relat_1(sK4,X0)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(unit_resulting_resolution,[],[f17313,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f17313,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(sK4,k3_subset_1(X0,X0)),k10_relat_1(sK4,X0))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f17035,f878])).

fof(f17035,plain,
    ( ! [X88,X87] : r1_tarski(k10_relat_1(sK4,k6_subset_1(X87,X88)),k10_relat_1(sK4,X87))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f278,f16903])).

fof(f278,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f130,f138])).

fof(f44740,plain,
    ( spl10_654
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_640 ),
    inference(avatar_split_clause,[],[f44279,f43912,f29016,f479,f174,f44738])).

fof(f44738,plain,
    ( spl10_654
  <=> u1_struct_0(sK2) = k6_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_654])])).

fof(f44279,plain,
    ( u1_struct_0(sK2) = k6_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k1_xboole_0))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_640 ),
    inference(forward_demodulation,[],[f44049,f29017])).

fof(f44049,plain,
    ( k6_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_640 ),
    inference(superposition,[],[f18460,f43913])).

fof(f18460,plain,
    ( ! [X12] : k6_subset_1(k10_relat_1(sK4,X12),k10_relat_1(sK4,k3_subset_1(X12,X12))) = k10_relat_1(sK4,X12)
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f910,f17179])).

fof(f17179,plain,
    ( ! [X2] : k3_subset_1(k10_relat_1(sK4,X2),k10_relat_1(sK4,X2)) = k10_relat_1(sK4,k3_subset_1(X2,X2))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17000,f878])).

fof(f17000,plain,
    ( ! [X2] : k3_subset_1(k10_relat_1(sK4,X2),k10_relat_1(sK4,X2)) = k10_relat_1(sK4,k6_subset_1(X2,X2))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f16903,f878])).

fof(f44576,plain,
    ( spl10_652
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43388,f43268,f29016,f479,f174,f44574])).

fof(f44574,plain,
    ( spl10_652
  <=> k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_652])])).

fof(f43268,plain,
    ( spl10_622
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_622])])).

fof(f43388,plain,
    ( k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_622 ),
    inference(backward_demodulation,[],[f43296,f29133])).

fof(f29133,plain,
    ( k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)) = k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(superposition,[],[f17179,f29017])).

fof(f43296,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))
    | ~ spl10_622 ),
    inference(forward_demodulation,[],[f43273,f43294])).

fof(f43294,plain,
    ( u1_struct_0(sK3) = k3_subset_1(u1_struct_0(sK3),k1_xboole_0)
    | ~ spl10_622 ),
    inference(forward_demodulation,[],[f43277,f152])).

fof(f43277,plain,
    ( k3_subset_1(u1_struct_0(sK3),k1_xboole_0) = k6_subset_1(u1_struct_0(sK3),k1_xboole_0)
    | ~ spl10_622 ),
    inference(unit_resulting_resolution,[],[f43269,f154])).

fof(f43269,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_622 ),
    inference(avatar_component_clause,[],[f43268])).

fof(f43273,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),k1_xboole_0))
    | ~ spl10_622 ),
    inference(unit_resulting_resolution,[],[f43269,f136])).

fof(f44375,plain,
    ( ~ spl10_651
    | spl10_285
    | spl10_617 ),
    inference(avatar_split_clause,[],[f44368,f40128,f25602,f44373])).

fof(f44373,plain,
    ( spl10_651
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_651])])).

fof(f25602,plain,
    ( spl10_285
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_285])])).

fof(f44368,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_285
    | ~ spl10_617 ),
    inference(unit_resulting_resolution,[],[f40129,f25603,f134])).

fof(f25603,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_285 ),
    inference(avatar_component_clause,[],[f25602])).

fof(f44367,plain,
    ( ~ spl10_649
    | ~ spl10_620 ),
    inference(avatar_split_clause,[],[f44347,f40146,f44365])).

fof(f44365,plain,
    ( spl10_649
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(k3_subset_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_649])])).

fof(f40146,plain,
    ( spl10_620
  <=> r2_hidden(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_620])])).

fof(f44347,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(k3_subset_1(u1_struct_0(sK3),sK5)))
    | ~ spl10_620 ),
    inference(unit_resulting_resolution,[],[f40147,f132])).

fof(f40147,plain,
    ( r2_hidden(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | ~ spl10_620 ),
    inference(avatar_component_clause,[],[f40146])).

fof(f44316,plain,
    ( ~ spl10_647
    | ~ spl10_644 ),
    inference(avatar_split_clause,[],[f44305,f44298,f44314])).

fof(f44314,plain,
    ( spl10_647
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_647])])).

fof(f44298,plain,
    ( spl10_644
  <=> r2_hidden(sK7(k1_xboole_0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_644])])).

fof(f44305,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(k1_xboole_0))
    | ~ spl10_644 ),
    inference(unit_resulting_resolution,[],[f44299,f132])).

fof(f44299,plain,
    ( r2_hidden(sK7(k1_xboole_0),u1_struct_0(sK3))
    | ~ spl10_644 ),
    inference(avatar_component_clause,[],[f44298])).

fof(f44300,plain,
    ( spl10_644
    | spl10_37
    | ~ spl10_642 ),
    inference(avatar_split_clause,[],[f44292,f44289,f318,f44298])).

fof(f318,plain,
    ( spl10_37
  <=> ~ v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_37])])).

fof(f44289,plain,
    ( spl10_642
  <=> m1_subset_1(sK7(k1_xboole_0),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_642])])).

fof(f44292,plain,
    ( r2_hidden(sK7(k1_xboole_0),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_642 ),
    inference(unit_resulting_resolution,[],[f319,f44290,f134])).

fof(f44290,plain,
    ( m1_subset_1(sK7(k1_xboole_0),u1_struct_0(sK3))
    | ~ spl10_642 ),
    inference(avatar_component_clause,[],[f44289])).

fof(f319,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl10_37 ),
    inference(avatar_component_clause,[],[f318])).

fof(f44291,plain,
    ( spl10_44
    | spl10_642
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43891,f43268,f44289,f393])).

fof(f393,plain,
    ( spl10_44
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f43891,plain,
    ( m1_subset_1(sK7(k1_xboole_0),u1_struct_0(sK3))
    | v1_xboole_0(k1_xboole_0)
    | ~ spl10_622 ),
    inference(resolution,[],[f43288,f360])).

fof(f43288,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_xboole_0)
        | m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl10_622 ),
    inference(resolution,[],[f43269,f146])).

fof(f43914,plain,
    ( spl10_640
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43296,f43268,f43912])).

fof(f43907,plain,
    ( spl10_638
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43294,f43268,f43905])).

fof(f43905,plain,
    ( spl10_638
  <=> u1_struct_0(sK3) = k3_subset_1(u1_struct_0(sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_638])])).

fof(f43887,plain,
    ( ~ spl10_637
    | spl10_235
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43276,f43268,f24775,f43885])).

fof(f43885,plain,
    ( spl10_637
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_637])])).

fof(f24775,plain,
    ( spl10_235
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_235])])).

fof(f43276,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k1_xboole_0)
    | ~ spl10_235
    | ~ spl10_622 ),
    inference(unit_resulting_resolution,[],[f24776,f43269,f146])).

fof(f24776,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_235 ),
    inference(avatar_component_clause,[],[f24775])).

fof(f43871,plain,
    ( spl10_634
    | spl10_229
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43279,f43268,f22415,f43869])).

fof(f43869,plain,
    ( spl10_634
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_634])])).

fof(f43279,plain,
    ( r2_hidden(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_622 ),
    inference(unit_resulting_resolution,[],[f22416,f43269,f134])).

fof(f43859,plain,
    ( ~ spl10_633
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | spl10_423
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43797,f43268,f29758,f29016,f479,f174,f43857])).

fof(f29758,plain,
    ( spl10_423
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_423])])).

fof(f43797,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2)
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_423
    | ~ spl10_622 ),
    inference(backward_demodulation,[],[f43388,f29759])).

fof(f29759,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ spl10_423 ),
    inference(avatar_component_clause,[],[f29758])).

fof(f43852,plain,
    ( ~ spl10_631
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | spl10_417
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43796,f43268,f29735,f29016,f479,f174,f43850])).

fof(f29735,plain,
    ( spl10_417
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_417])])).

fof(f43796,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK4,k1_xboole_0),sK2)
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_417
    | ~ spl10_622 ),
    inference(backward_demodulation,[],[f43388,f29736])).

fof(f29736,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ spl10_417 ),
    inference(avatar_component_clause,[],[f29735])).

fof(f43840,plain,
    ( spl10_628
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43274,f43268,f43838])).

fof(f43838,plain,
    ( spl10_628
  <=> r1_tarski(k1_xboole_0,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_628])])).

fof(f43274,plain,
    ( r1_tarski(k1_xboole_0,u1_struct_0(sK3))
    | ~ spl10_622 ),
    inference(unit_resulting_resolution,[],[f43269,f138])).

fof(f43829,plain,
    ( ~ spl10_627
    | spl10_445
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43389,f43268,f32841,f43827])).

fof(f32841,plain,
    ( spl10_445
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_445])])).

fof(f43389,plain,
    ( ~ v3_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_445
    | ~ spl10_622 ),
    inference(backward_demodulation,[],[f43296,f32842])).

fof(f32842,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | ~ spl10_445 ),
    inference(avatar_component_clause,[],[f32841])).

fof(f43822,plain,
    ( ~ spl10_625
    | spl10_157
    | ~ spl10_622 ),
    inference(avatar_split_clause,[],[f43312,f43268,f10817,f43820])).

fof(f10817,plain,
    ( spl10_157
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_157])])).

fof(f43312,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK3)
    | ~ spl10_157
    | ~ spl10_622 ),
    inference(backward_demodulation,[],[f43296,f10818])).

fof(f10818,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | ~ spl10_157 ),
    inference(avatar_component_clause,[],[f10817])).

fof(f43271,plain,
    ( spl10_44
    | ~ spl10_616 ),
    inference(avatar_split_clause,[],[f40941,f40131,f393])).

fof(f40131,plain,
    ( spl10_616
  <=> v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_616])])).

fof(f40941,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_616 ),
    inference(backward_demodulation,[],[f40149,f40132])).

fof(f40132,plain,
    ( v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_616 ),
    inference(avatar_component_clause,[],[f40131])).

fof(f40149,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK3),sK5)
    | ~ spl10_616 ),
    inference(unit_resulting_resolution,[],[f40132,f112])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t6_boole)).

fof(f43270,plain,
    ( spl10_622
    | ~ spl10_274
    | ~ spl10_616 ),
    inference(avatar_split_clause,[],[f40804,f40131,f25503,f43268])).

fof(f40804,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274
    | ~ spl10_616 ),
    inference(backward_demodulation,[],[f40149,f25504])).

fof(f40148,plain,
    ( spl10_620
    | spl10_37
    | ~ spl10_618 ),
    inference(avatar_split_clause,[],[f40140,f40137,f318,f40146])).

fof(f40137,plain,
    ( spl10_618
  <=> m1_subset_1(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_618])])).

fof(f40140,plain,
    ( r2_hidden(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_618 ),
    inference(unit_resulting_resolution,[],[f319,f40138,f134])).

fof(f40138,plain,
    ( m1_subset_1(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | ~ spl10_618 ),
    inference(avatar_component_clause,[],[f40137])).

fof(f40139,plain,
    ( spl10_616
    | spl10_618
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f27211,f25503,f40137,f40131])).

fof(f27211,plain,
    ( m1_subset_1(sK7(k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | v1_xboole_0(k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_274 ),
    inference(resolution,[],[f25523,f360])).

fof(f25523,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_subset_1(u1_struct_0(sK3),sK5))
        | m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl10_274 ),
    inference(resolution,[],[f25504,f146])).

fof(f40117,plain,
    ( spl10_614
    | spl10_229
    | ~ spl10_604 ),
    inference(avatar_split_clause,[],[f40015,f39991,f22415,f40115])).

fof(f40115,plain,
    ( spl10_614
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_614])])).

fof(f39991,plain,
    ( spl10_604
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_604])])).

fof(f40015,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_604 ),
    inference(unit_resulting_resolution,[],[f22416,f39992,f134])).

fof(f39992,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_604 ),
    inference(avatar_component_clause,[],[f39991])).

fof(f40110,plain,
    ( ~ spl10_613
    | spl10_235
    | ~ spl10_604 ),
    inference(avatar_split_clause,[],[f40012,f39991,f24775,f40108])).

fof(f40108,plain,
    ( spl10_613
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_613])])).

fof(f40012,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))))
    | ~ spl10_235
    | ~ spl10_604 ),
    inference(unit_resulting_resolution,[],[f24776,f39992,f146])).

fof(f40045,plain,
    ( spl10_610
    | ~ spl10_604 ),
    inference(avatar_split_clause,[],[f40010,f39991,f40043])).

fof(f40043,plain,
    ( spl10_610
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_610])])).

fof(f40010,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_604 ),
    inference(unit_resulting_resolution,[],[f39992,f138])).

fof(f40007,plain,
    ( spl10_608
    | ~ spl10_550 ),
    inference(avatar_split_clause,[],[f38743,f38740,f40005])).

fof(f40005,plain,
    ( spl10_608
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_608])])).

fof(f38740,plain,
    ( spl10_550
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_550])])).

fof(f38743,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_550 ),
    inference(unit_resulting_resolution,[],[f38741,f139])).

fof(f38741,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),u1_struct_0(sK3))
    | ~ spl10_550 ),
    inference(avatar_component_clause,[],[f38740])).

fof(f40000,plain,
    ( spl10_606
    | ~ spl10_334 ),
    inference(avatar_split_clause,[],[f27149,f27122,f39998])).

fof(f39998,plain,
    ( spl10_606
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_606])])).

fof(f27122,plain,
    ( spl10_334
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_334])])).

fof(f27149,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_334 ),
    inference(unit_resulting_resolution,[],[f27123,f135])).

fof(f27123,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_334 ),
    inference(avatar_component_clause,[],[f27122])).

fof(f39993,plain,
    ( spl10_604
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f27136,f27115,f39991])).

fof(f27115,plain,
    ( spl10_332
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_332])])).

fof(f27136,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_332 ),
    inference(resolution,[],[f27116,f135])).

fof(f27116,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_332 ),
    inference(avatar_component_clause,[],[f27115])).

fof(f39975,plain,
    ( spl10_602
    | ~ spl10_218
    | spl10_229 ),
    inference(avatar_split_clause,[],[f39686,f22415,f22323,f39973])).

fof(f39973,plain,
    ( spl10_602
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_602])])).

fof(f22323,plain,
    ( spl10_218
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_218])])).

fof(f39686,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218
    | ~ spl10_229 ),
    inference(superposition,[],[f39193,f907])).

fof(f39193,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f22345,f134])).

fof(f22345,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218 ),
    inference(forward_demodulation,[],[f22329,f22331])).

fof(f22331,plain,
    ( ! [X0] : k6_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0) = k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0)
    | ~ spl10_218 ),
    inference(unit_resulting_resolution,[],[f22324,f155])).

fof(f22324,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218 ),
    inference(avatar_component_clause,[],[f22323])).

fof(f22329,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218 ),
    inference(unit_resulting_resolution,[],[f22324,f142])).

fof(f39968,plain,
    ( ~ spl10_601
    | ~ spl10_218
    | spl10_235 ),
    inference(avatar_split_clause,[],[f39670,f24775,f22323,f39966])).

fof(f39966,plain,
    ( spl10_601
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_601])])).

fof(f39670,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))))
    | ~ spl10_218
    | ~ spl10_235 ),
    inference(superposition,[],[f39190,f907])).

fof(f39190,plain,
    ( ! [X0] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k6_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X0))
    | ~ spl10_218
    | ~ spl10_235 ),
    inference(unit_resulting_resolution,[],[f24776,f22345,f146])).

fof(f39961,plain,
    ( ~ spl10_599
    | spl10_235
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f39649,f25372,f24775,f39959])).

fof(f39959,plain,
    ( spl10_599
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_599])])).

fof(f39649,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))))
    | ~ spl10_235
    | ~ spl10_262 ),
    inference(superposition,[],[f38957,f907])).

fof(f38957,plain,
    ( ! [X0] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0)))
    | ~ spl10_235
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f24776,f26718,f146])).

fof(f26718,plain,
    ( ! [X0] : m1_subset_1(k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25402,f135])).

fof(f25402,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(k3_subset_1(sK5,sK5),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(forward_demodulation,[],[f25385,f25388])).

fof(f25388,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(sK5,sK5),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5),X0)
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25373,f155])).

fof(f25385,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25373,f142])).

fof(f39954,plain,
    ( spl10_596
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f33600,f25372,f39952])).

fof(f39952,plain,
    ( spl10_596
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_596])])).

fof(f33600,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)))),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(superposition,[],[f33585,f878])).

fof(f33585,plain,
    ( ! [X3] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(k3_subset_1(sK5,sK5),X3))),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(superposition,[],[f33536,f907])).

fof(f33536,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(k3_subset_1(sK5,sK5),X0),X1),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f26745,f138])).

fof(f26745,plain,
    ( ! [X0,X1] : m1_subset_1(k6_subset_1(k6_subset_1(k3_subset_1(sK5,sK5),X0),X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(forward_demodulation,[],[f26721,f26724])).

fof(f26724,plain,
    ( ! [X0,X1] : k6_subset_1(k6_subset_1(k3_subset_1(sK5,sK5),X0),X1) = k7_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0),X1)
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25402,f155])).

fof(f26721,plain,
    ( ! [X0,X1] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0),X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25402,f142])).

fof(f39940,plain,
    ( ~ spl10_595
    | spl10_235 ),
    inference(avatar_split_clause,[],[f24949,f24775,f39938])).

fof(f39938,plain,
    ( spl10_595
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_595])])).

fof(f24949,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))))))
    | ~ spl10_235 ),
    inference(unit_resulting_resolution,[],[f24776,f3230])).

fof(f3230,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X6)))))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f2291,f146])).

fof(f2291,plain,(
    ! [X0] : m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X0)))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f2277,f139])).

fof(f2277,plain,(
    ! [X3] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X3)))))),X3) ),
    inference(superposition,[],[f2260,f907])).

fof(f2260,plain,(
    ! [X6,X7] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X6)))),X7),X6) ),
    inference(superposition,[],[f2220,f907])).

fof(f2220,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X2),X0) ),
    inference(unit_resulting_resolution,[],[f1452,f138])).

fof(f1452,plain,(
    ! [X2,X0,X1] : m1_subset_1(k6_subset_1(k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X2),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f1451,f1422])).

fof(f1422,plain,(
    ! [X2,X0,X1] : m1_subset_1(k7_subset_1(X0,k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X2),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f1398,f791])).

fof(f791,plain,(
    ! [X2,X0,X1] : m1_subset_1(k7_subset_1(X0,k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1),X2),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f742,f142])).

fof(f1451,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X2) = k7_subset_1(X0,k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X2) ),
    inference(forward_demodulation,[],[f1396,f1398])).

fof(f1396,plain,(
    ! [X2,X0,X1] : k6_subset_1(k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1),X2) = k7_subset_1(X0,k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1),X2) ),
    inference(unit_resulting_resolution,[],[f742,f155])).

fof(f39924,plain,
    ( spl10_586
    | spl10_229
    | ~ spl10_572 ),
    inference(avatar_split_clause,[],[f39741,f39476,f22415,f39738])).

fof(f39738,plain,
    ( spl10_586
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_586])])).

fof(f39476,plain,
    ( spl10_572
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_572])])).

fof(f39741,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_572 ),
    inference(subsumption_resolution,[],[f39551,f22416])).

fof(f39551,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_572 ),
    inference(resolution,[],[f39477,f134])).

fof(f39477,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_572 ),
    inference(avatar_component_clause,[],[f39476])).

fof(f39871,plain,
    ( ~ spl10_593
    | ~ spl10_574 ),
    inference(avatar_split_clause,[],[f39560,f39499,f39869])).

fof(f39869,plain,
    ( spl10_593
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_593])])).

fof(f39499,plain,
    ( spl10_574
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_574])])).

fof(f39560,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))))
    | ~ spl10_574 ),
    inference(unit_resulting_resolution,[],[f39500,f132])).

fof(f39500,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_574 ),
    inference(avatar_component_clause,[],[f39499])).

fof(f39864,plain,
    ( ~ spl10_591
    | spl10_235
    | ~ spl10_572 ),
    inference(avatar_split_clause,[],[f39535,f39476,f24775,f39862])).

fof(f39862,plain,
    ( spl10_591
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_591])])).

fof(f39535,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))))
    | ~ spl10_235
    | ~ spl10_572 ),
    inference(unit_resulting_resolution,[],[f24776,f39477,f146])).

fof(f39857,plain,
    ( ~ spl10_589
    | spl10_235
    | ~ spl10_570 ),
    inference(avatar_split_clause,[],[f39510,f39453,f24775,f39855])).

fof(f39855,plain,
    ( spl10_589
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_589])])).

fof(f39453,plain,
    ( spl10_570
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_570])])).

fof(f39510,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))))
    | ~ spl10_235
    | ~ spl10_570 ),
    inference(unit_resulting_resolution,[],[f24776,f39454,f146])).

fof(f39454,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_570 ),
    inference(avatar_component_clause,[],[f39453])).

fof(f39758,plain,
    ( spl10_320
    | ~ spl10_340 ),
    inference(avatar_split_clause,[],[f39105,f27287,f26983])).

fof(f26983,plain,
    ( spl10_320
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_320])])).

fof(f27287,plain,
    ( spl10_340
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_340])])).

fof(f39105,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_340 ),
    inference(superposition,[],[f39071,f910])).

fof(f39071,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X0),u1_struct_0(sK3))
    | ~ spl10_340 ),
    inference(unit_resulting_resolution,[],[f27675,f138])).

fof(f27675,plain,
    ( ! [X2] : m1_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_340 ),
    inference(forward_demodulation,[],[f27661,f27653])).

fof(f27653,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X0)
    | ~ spl10_340 ),
    inference(unit_resulting_resolution,[],[f27288,f155])).

fof(f27288,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_340 ),
    inference(avatar_component_clause,[],[f27287])).

fof(f27661,plain,
    ( ! [X2] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_340 ),
    inference(resolution,[],[f27288,f142])).

fof(f39756,plain,
    ( spl10_340
    | ~ spl10_386 ),
    inference(avatar_split_clause,[],[f36972,f28184,f27287])).

fof(f28184,plain,
    ( spl10_386
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_386])])).

fof(f36972,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(resolution,[],[f28185,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t1_subset)).

fof(f28185,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(avatar_component_clause,[],[f28184])).

fof(f39755,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39754])).

fof(f39754,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f36972,f27285])).

fof(f27285,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_341 ),
    inference(avatar_component_clause,[],[f27284])).

fof(f27284,plain,
    ( spl10_341
  <=> ~ m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_341])])).

fof(f39753,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39752])).

fof(f39752,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f36966,f27285])).

fof(f36966,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(unit_resulting_resolution,[],[f225,f28185,f146])).

fof(f39751,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39750])).

fof(f39750,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f36968,f27285])).

fof(f36968,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(unit_resulting_resolution,[],[f28185,f133])).

fof(f39749,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39748])).

fof(f39748,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f28562,f27285])).

fof(f28562,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(resolution,[],[f28185,f133])).

fof(f39747,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39746])).

fof(f39746,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f28556,f27285])).

fof(f28556,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(unit_resulting_resolution,[],[f225,f28185,f146])).

fof(f39745,plain,
    ( spl10_341
    | ~ spl10_386 ),
    inference(avatar_contradiction_clause,[],[f39744])).

fof(f39744,plain,
    ( $false
    | ~ spl10_341
    | ~ spl10_386 ),
    inference(subsumption_resolution,[],[f28558,f27285])).

fof(f28558,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_386 ),
    inference(unit_resulting_resolution,[],[f28185,f133])).

fof(f39743,plain,
    ( ~ spl10_320
    | spl10_341 ),
    inference(avatar_contradiction_clause,[],[f39742])).

fof(f39742,plain,
    ( $false
    | ~ spl10_320
    | ~ spl10_341 ),
    inference(subsumption_resolution,[],[f27285,f27023])).

fof(f27023,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_320 ),
    inference(unit_resulting_resolution,[],[f26984,f139])).

fof(f26984,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_320 ),
    inference(avatar_component_clause,[],[f26983])).

fof(f39740,plain,
    ( spl10_586
    | spl10_229
    | ~ spl10_340 ),
    inference(avatar_split_clause,[],[f39468,f27287,f22415,f39738])).

fof(f39468,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_340 ),
    inference(superposition,[],[f39076,f907])).

fof(f39076,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_340 ),
    inference(unit_resulting_resolution,[],[f22416,f27675,f134])).

fof(f39733,plain,
    ( spl10_584
    | spl10_229
    | ~ spl10_338 ),
    inference(avatar_split_clause,[],[f39445,f27280,f22415,f39731])).

fof(f39731,plain,
    ( spl10_584
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_584])])).

fof(f27280,plain,
    ( spl10_338
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_338])])).

fof(f39445,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_338 ),
    inference(superposition,[],[f39021,f907])).

fof(f39021,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_338 ),
    inference(unit_resulting_resolution,[],[f22416,f27638,f134])).

fof(f27638,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_338 ),
    inference(forward_demodulation,[],[f27620,f27623])).

fof(f27623,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0)
    | ~ spl10_338 ),
    inference(unit_resulting_resolution,[],[f27281,f155])).

fof(f27281,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_338 ),
    inference(avatar_component_clause,[],[f27280])).

fof(f27620,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_338 ),
    inference(unit_resulting_resolution,[],[f27281,f142])).

fof(f39726,plain,
    ( spl10_582
    | spl10_229
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f39429,f25372,f22415,f39724])).

fof(f39724,plain,
    ( spl10_582
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_582])])).

fof(f39429,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(superposition,[],[f38960,f907])).

fof(f38960,plain,
    ( ! [X0] : r2_hidden(k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f22416,f26718,f134])).

fof(f39624,plain,
    ( ~ spl10_581
    | spl10_235
    | ~ spl10_536 ),
    inference(avatar_split_clause,[],[f38550,f38449,f24775,f39622])).

fof(f39622,plain,
    ( spl10_581
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_581])])).

fof(f38449,plain,
    ( spl10_536
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_536])])).

fof(f38550,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))))
    | ~ spl10_235
    | ~ spl10_536 ),
    inference(unit_resulting_resolution,[],[f24776,f38450,f146])).

fof(f38450,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_536 ),
    inference(avatar_component_clause,[],[f38449])).

fof(f39617,plain,
    ( spl10_578
    | ~ spl10_538 ),
    inference(avatar_split_clause,[],[f38544,f38541,f39615])).

fof(f39615,plain,
    ( spl10_578
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_578])])).

fof(f38541,plain,
    ( spl10_538
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_538])])).

fof(f38544,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_538 ),
    inference(unit_resulting_resolution,[],[f38542,f139])).

fof(f38542,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),u1_struct_0(sK3))
    | ~ spl10_538 ),
    inference(avatar_component_clause,[],[f38541])).

fof(f39587,plain,
    ( spl10_576
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24742,f22415,f39585])).

fof(f39585,plain,
    ( spl10_576
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_576])])).

fof(f24742,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f2291,f22416,f134])).

fof(f39501,plain,
    ( spl10_574
    | spl10_229
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f39161,f25503,f22415,f39499])).

fof(f39161,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_274 ),
    inference(superposition,[],[f38624,f907])).

fof(f38624,plain,
    ( ! [X0] : r2_hidden(sK7(k1_zfmisc_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f22416,f38495,f134])).

fof(f38495,plain,
    ( ! [X3] : m1_subset_1(sK7(k1_zfmisc_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(superposition,[],[f27245,f907])).

fof(f27245,plain,
    ( ! [X8,X9] : m1_subset_1(k6_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X8),X9),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(forward_demodulation,[],[f27229,f27221])).

fof(f27221,plain,
    ( ! [X0,X1] : k6_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0),X1) = k7_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0),X1)
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25529,f155])).

fof(f27229,plain,
    ( ! [X8,X9] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X8),X9),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(resolution,[],[f25529,f142])).

fof(f39478,plain,
    ( spl10_572
    | ~ spl10_340 ),
    inference(avatar_split_clause,[],[f39093,f27287,f39476])).

fof(f39093,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_340 ),
    inference(superposition,[],[f27675,f907])).

fof(f39455,plain,
    ( spl10_570
    | ~ spl10_338 ),
    inference(avatar_split_clause,[],[f39038,f27280,f39453])).

fof(f39038,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_338 ),
    inference(superposition,[],[f27638,f907])).

fof(f39361,plain,
    ( spl10_568
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f29279,f25372,f39359])).

fof(f39359,plain,
    ( spl10_568
  <=> r1_tarski(k3_subset_1(k3_subset_1(sK5,sK5),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_568])])).

fof(f29279,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(sK5,sK5),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(superposition,[],[f26731,f890])).

fof(f890,plain,(
    ! [X0] : k3_subset_1(X0,sK7(k1_zfmisc_1(X0))) = k6_subset_1(X0,sK7(k1_zfmisc_1(X0))) ),
    inference(unit_resulting_resolution,[],[f129,f154])).

fof(f26731,plain,
    ( ! [X7] : r1_tarski(k6_subset_1(k3_subset_1(sK5,sK5),X7),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(resolution,[],[f25402,f138])).

fof(f39180,plain,
    ( spl10_566
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22303,f22231,f39178])).

fof(f39178,plain,
    ( spl10_566
  <=> r1_tarski(k3_subset_1(sK6(sK2,sK4,sK3),sK6(sK2,sK4,sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_566])])).

fof(f22303,plain,
    ( r1_tarski(k3_subset_1(sK6(sK2,sK4,sK3),sK6(sK2,sK4,sK3)),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(superposition,[],[f22273,f878])).

fof(f22273,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK6(sK2,sK4,sK3),X0),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22254,f138])).

fof(f22254,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(sK6(sK2,sK4,sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(forward_demodulation,[],[f22238,f22240])).

fof(f22240,plain,
    ( ! [X0] : k6_subset_1(sK6(sK2,sK4,sK3),X0) = k7_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3),X0)
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22232,f155])).

fof(f22238,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22232,f142])).

fof(f39148,plain,
    ( spl10_564
    | spl10_229
    | ~ spl10_536 ),
    inference(avatar_split_clause,[],[f38553,f38449,f22415,f39146])).

fof(f39146,plain,
    ( spl10_564
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_564])])).

fof(f38553,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_536 ),
    inference(unit_resulting_resolution,[],[f22416,f38450,f134])).

fof(f39116,plain,
    ( spl10_562
    | ~ spl10_340 ),
    inference(avatar_split_clause,[],[f39106,f27287,f39114])).

fof(f39114,plain,
    ( spl10_562
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_562])])).

fof(f39106,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_340 ),
    inference(superposition,[],[f39071,f907])).

fof(f39061,plain,
    ( spl10_560
    | ~ spl10_338 ),
    inference(avatar_split_clause,[],[f39051,f27280,f39059])).

fof(f39059,plain,
    ( spl10_560
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_560])])).

fof(f39051,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))),u1_struct_0(sK3))
    | ~ spl10_338 ),
    inference(superposition,[],[f39016,f907])).

fof(f39016,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),X0),u1_struct_0(sK3))
    | ~ spl10_338 ),
    inference(unit_resulting_resolution,[],[f27638,f138])).

fof(f39006,plain,
    ( spl10_558
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f38996,f25372,f39004])).

fof(f39004,plain,
    ( spl10_558
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_558])])).

fof(f38996,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(superposition,[],[f38955,f907])).

fof(f38955,plain,
    ( ! [X0] : r1_tarski(k3_subset_1(u1_struct_0(sK3),k6_subset_1(k3_subset_1(sK5,sK5),X0)),u1_struct_0(sK3))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f26718,f138])).

fof(f38772,plain,
    ( ~ spl10_557
    | ~ spl10_2
    | spl10_555 ),
    inference(avatar_split_clause,[],[f38765,f38762,f167,f38770])).

fof(f38770,plain,
    ( spl10_557
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3)))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_557])])).

fof(f38762,plain,
    ( spl10_555
  <=> ~ v3_pre_topc(sK7(k1_zfmisc_1(u1_struct_0(sK3))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_555])])).

fof(f38765,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3)))),sK3)
    | ~ spl10_2
    | ~ spl10_555 ),
    inference(unit_resulting_resolution,[],[f168,f129,f38763,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f38763,plain,
    ( ~ v3_pre_topc(sK7(k1_zfmisc_1(u1_struct_0(sK3))),sK3)
    | ~ spl10_555 ),
    inference(avatar_component_clause,[],[f38762])).

fof(f38764,plain,
    ( spl10_552
    | ~ spl10_555
    | spl10_19
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f5185,f295,f231,f38762,f38756])).

fof(f38756,plain,
    ( spl10_552
  <=> v3_pre_topc(k10_relat_1(sK4,sK7(k1_zfmisc_1(u1_struct_0(sK3)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_552])])).

fof(f5185,plain,
    ( ~ v3_pre_topc(sK7(k1_zfmisc_1(u1_struct_0(sK3))),sK3)
    | v3_pre_topc(k10_relat_1(sK4,sK7(k1_zfmisc_1(u1_struct_0(sK3)))),sK2)
    | ~ spl10_19
    | ~ spl10_30 ),
    inference(resolution,[],[f3734,f129])).

fof(f38742,plain,
    ( spl10_550
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f38723,f22231,f38740])).

fof(f38723,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(superposition,[],[f38707,f907])).

fof(f38707,plain,
    ( ! [X3] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),X3),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(superposition,[],[f38665,f907])).

fof(f38665,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(sK6(sK2,sK4,sK3),X0),X1),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22297,f138])).

fof(f22297,plain,
    ( ! [X0,X1] : m1_subset_1(k6_subset_1(k6_subset_1(sK6(sK2,sK4,sK3),X0),X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(forward_demodulation,[],[f22274,f22276])).

fof(f22276,plain,
    ( ! [X0,X1] : k6_subset_1(k6_subset_1(sK6(sK2,sK4,sK3),X0),X1) = k7_subset_1(u1_struct_0(sK3),k6_subset_1(sK6(sK2,sK4,sK3),X0),X1)
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22254,f155])).

fof(f22274,plain,
    ( ! [X0,X1] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k6_subset_1(sK6(sK2,sK4,sK3),X0),X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22254,f142])).

fof(f38613,plain,
    ( ~ spl10_549
    | ~ spl10_2
    | ~ spl10_262
    | spl10_547 ),
    inference(avatar_split_clause,[],[f38606,f38603,f25372,f167,f38611])).

fof(f38611,plain,
    ( spl10_549
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_549])])).

fof(f38603,plain,
    ( spl10_547
  <=> ~ v3_pre_topc(k3_subset_1(sK5,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_547])])).

fof(f38606,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),sK3)
    | ~ spl10_2
    | ~ spl10_262
    | ~ spl10_547 ),
    inference(unit_resulting_resolution,[],[f168,f25373,f38604,f126])).

fof(f38604,plain,
    ( ~ v3_pre_topc(k3_subset_1(sK5,sK5),sK3)
    | ~ spl10_547 ),
    inference(avatar_component_clause,[],[f38603])).

fof(f38605,plain,
    ( spl10_544
    | ~ spl10_547
    | ~ spl10_30
    | spl10_149
    | ~ spl10_206
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f33150,f25372,f22198,f6699,f295,f38603,f38597])).

fof(f38597,plain,
    ( spl10_544
  <=> v3_pre_topc(k10_relat_1(sK4,k3_subset_1(sK5,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_544])])).

fof(f6699,plain,
    ( spl10_149
  <=> ~ sP0(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_149])])).

fof(f22198,plain,
    ( spl10_206
  <=> sP1(sK3,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_206])])).

fof(f33150,plain,
    ( ~ v3_pre_topc(k3_subset_1(sK5,sK5),sK3)
    | v3_pre_topc(k10_relat_1(sK4,k3_subset_1(sK5,sK5)),sK2)
    | ~ spl10_30
    | ~ spl10_149
    | ~ spl10_206
    | ~ spl10_262 ),
    inference(resolution,[],[f28751,f25373])).

fof(f28751,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v3_pre_topc(X4,sK3)
        | v3_pre_topc(k10_relat_1(sK4,X4),sK2) )
    | ~ spl10_30
    | ~ spl10_149
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f24530,f22205])).

fof(f22205,plain,
    ( ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ spl10_149
    | ~ spl10_206 ),
    inference(unit_resulting_resolution,[],[f22199,f6700,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v5_pre_topc(X1,X2,X0)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( ( v5_pre_topc(X1,X2,X0)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ v5_pre_topc(X1,X2,X0) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X1,X2,X0] :
      ( ( ( v5_pre_topc(X2,X0,X1)
          | ~ sP0(X0,X2,X1) )
        & ( sP0(X0,X2,X1)
          | ~ v5_pre_topc(X2,X0,X1) ) )
      | ~ sP1(X1,X2,X0) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X1,X2,X0] :
      ( ( v5_pre_topc(X2,X0,X1)
      <=> sP0(X0,X2,X1) )
      | ~ sP1(X1,X2,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f6700,plain,
    ( ~ sP0(sK2,sK4,sK3)
    | ~ spl10_149 ),
    inference(avatar_component_clause,[],[f6699])).

fof(f22199,plain,
    ( sP1(sK3,sK4,sK2)
    | ~ spl10_206 ),
    inference(avatar_component_clause,[],[f22198])).

fof(f24530,plain,
    ( ! [X4] :
        ( v3_pre_topc(k10_relat_1(sK4,X4),sK2)
        | ~ v3_pre_topc(X4,sK3)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK3)))
        | v5_pre_topc(sK4,sK2,sK3) )
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f106,f3662])).

fof(f38592,plain,
    ( spl10_542
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f29330,f25503,f38590])).

fof(f38590,plain,
    ( spl10_542
  <=> r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_542])])).

fof(f29330,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(superposition,[],[f27228,f878])).

fof(f27228,plain,
    ( ! [X7] : r1_tarski(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X7),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(resolution,[],[f25529,f138])).

fof(f38583,plain,
    ( spl10_540
    | ~ spl10_536 ),
    inference(avatar_split_clause,[],[f38548,f38449,f38581])).

fof(f38581,plain,
    ( spl10_540
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_540])])).

fof(f38548,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),u1_struct_0(sK3))
    | ~ spl10_536 ),
    inference(unit_resulting_resolution,[],[f38450,f138])).

fof(f38543,plain,
    ( spl10_538
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f38524,f25503,f38541])).

fof(f38524,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(superposition,[],[f38508,f907])).

fof(f38508,plain,
    ( ! [X3] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),X3),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(superposition,[],[f38466,f907])).

fof(f38466,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),X0),X1),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f27245,f138])).

fof(f38451,plain,
    ( spl10_536
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f26100,f26052,f38449])).

fof(f26052,plain,
    ( spl10_304
  <=> m1_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_304])])).

fof(f26100,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f26053,f135])).

fof(f26053,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_304 ),
    inference(avatar_component_clause,[],[f26052])).

fof(f38435,plain,
    ( spl10_534
    | spl10_229
    | ~ spl10_518 ),
    inference(avatar_split_clause,[],[f38370,f38023,f22415,f38433])).

fof(f38433,plain,
    ( spl10_534
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_534])])).

fof(f38023,plain,
    ( spl10_518
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_518])])).

fof(f38370,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_518 ),
    inference(unit_resulting_resolution,[],[f22416,f38024,f134])).

fof(f38024,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_518 ),
    inference(avatar_component_clause,[],[f38023])).

fof(f38362,plain,
    ( ~ spl10_533
    | spl10_473 ),
    inference(avatar_split_clause,[],[f36555,f36550,f38360])).

fof(f38360,plain,
    ( spl10_533
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_533])])).

fof(f36550,plain,
    ( spl10_473
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_473])])).

fof(f36555,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_473 ),
    inference(unit_resulting_resolution,[],[f513,f36551,f146])).

fof(f36551,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_473 ),
    inference(avatar_component_clause,[],[f36550])).

fof(f38341,plain,
    ( ~ spl10_531
    | spl10_437 ),
    inference(avatar_split_clause,[],[f32770,f32593,f38339])).

fof(f38339,plain,
    ( spl10_531
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_531])])).

fof(f32593,plain,
    ( spl10_437
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_437])])).

fof(f32770,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))))
    | ~ spl10_437 ),
    inference(unit_resulting_resolution,[],[f32594,f3310])).

fof(f3310,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(X6,X6))))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f2501,f146])).

fof(f2501,plain,(
    ! [X0] : m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(X0,X0))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f2477,f139])).

fof(f2477,plain,(
    ! [X3] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(X3,X3))))),X3) ),
    inference(superposition,[],[f2426,f907])).

fof(f2426,plain,(
    ! [X6,X7] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k3_subset_1(X6,X6))),X7),X6) ),
    inference(superposition,[],[f2398,f907])).

fof(f2398,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(k3_subset_1(X0,X0),X1),X2),X0) ),
    inference(superposition,[],[f2355,f878])).

fof(f2355,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X0) ),
    inference(unit_resulting_resolution,[],[f1496,f138])).

fof(f1496,plain,(
    ! [X2,X0,X3,X1] : m1_subset_1(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f1389,f1454])).

fof(f1454,plain,(
    ! [X2,X0,X3,X1] : m1_subset_1(k6_subset_1(k7_subset_1(X0,k6_subset_1(X0,X1),X2),X3),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f1394,f772])).

fof(f772,plain,(
    ! [X2,X0,X3,X1] : m1_subset_1(k7_subset_1(X0,k7_subset_1(X0,k6_subset_1(X0,X1),X2),X3),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f740,f142])).

fof(f740,plain,(
    ! [X2,X0,X1] : m1_subset_1(k7_subset_1(X0,k6_subset_1(X0,X1),X2),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f130,f142])).

fof(f1394,plain,(
    ! [X2,X0,X3,X1] : k6_subset_1(k7_subset_1(X0,k6_subset_1(X0,X1),X2),X3) = k7_subset_1(X0,k7_subset_1(X0,k6_subset_1(X0,X1),X2),X3) ),
    inference(unit_resulting_resolution,[],[f740,f155])).

fof(f1389,plain,(
    ! [X2,X0,X1] : k6_subset_1(k6_subset_1(X0,X1),X2) = k7_subset_1(X0,k6_subset_1(X0,X1),X2) ),
    inference(unit_resulting_resolution,[],[f130,f155])).

fof(f32594,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK5)
    | ~ spl10_437 ),
    inference(avatar_component_clause,[],[f32593])).

fof(f38320,plain,
    ( ~ spl10_529
    | spl10_437 ),
    inference(avatar_split_clause,[],[f32767,f32593,f38318])).

fof(f38318,plain,
    ( spl10_529
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_529])])).

fof(f32767,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))))
    | ~ spl10_437 ),
    inference(unit_resulting_resolution,[],[f32594,f3230])).

fof(f38306,plain,
    ( ~ spl10_527
    | spl10_437 ),
    inference(avatar_split_clause,[],[f32765,f32593,f38304])).

fof(f38304,plain,
    ( spl10_527
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_527])])).

fof(f32765,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))))
    | ~ spl10_437 ),
    inference(unit_resulting_resolution,[],[f32594,f3170])).

fof(f3170,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_subset_1(X6,sK7(k1_zfmisc_1(k3_subset_1(X6,X6)))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f1849,f146])).

fof(f1849,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK7(k1_zfmisc_1(k3_subset_1(X0,X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1683,f135])).

fof(f1683,plain,(
    ! [X0] : m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(X0,X0))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1665,f139])).

fof(f1665,plain,(
    ! [X0] : r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(X0,X0))),X0) ),
    inference(superposition,[],[f1656,f878])).

fof(f1656,plain,(
    ! [X6,X7] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(X6,X7))),X6) ),
    inference(superposition,[],[f1476,f907])).

fof(f1476,plain,(
    ! [X2,X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(X0,X1),X2),X0) ),
    inference(backward_demodulation,[],[f1389,f775])).

fof(f775,plain,(
    ! [X2,X0,X1] : r1_tarski(k7_subset_1(X0,k6_subset_1(X0,X1),X2),X0) ),
    inference(unit_resulting_resolution,[],[f740,f138])).

fof(f38285,plain,
    ( ~ spl10_525
    | spl10_437 ),
    inference(avatar_split_clause,[],[f32763,f32593,f38283])).

fof(f38283,plain,
    ( spl10_525
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_525])])).

fof(f32763,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))))
    | ~ spl10_437 ),
    inference(unit_resulting_resolution,[],[f32594,f3059])).

fof(f3059,plain,(
    ! [X14,X15] :
      ( ~ r2_hidden(X15,sK7(k1_zfmisc_1(k3_subset_1(X14,sK7(k1_zfmisc_1(X14))))))
      | m1_subset_1(X15,X14) ) ),
    inference(superposition,[],[f1833,f890])).

fof(f1833,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,sK7(k1_zfmisc_1(k6_subset_1(X10,X11))))
      | m1_subset_1(X9,X10) ) ),
    inference(resolution,[],[f1663,f146])).

fof(f1663,plain,(
    ! [X0,X1] : m1_subset_1(sK7(k1_zfmisc_1(k6_subset_1(X0,X1))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1656,f139])).

fof(f38254,plain,
    ( ~ spl10_523
    | spl10_437 ),
    inference(avatar_split_clause,[],[f32759,f32593,f38252])).

fof(f38252,plain,
    ( spl10_523
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_523])])).

fof(f32759,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))))
    | ~ spl10_437 ),
    inference(unit_resulting_resolution,[],[f32594,f2968])).

fof(f2968,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,k3_subset_1(X6,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X6))))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f1802,f146])).

fof(f1802,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X0))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1660,f135])).

fof(f1660,plain,(
    ! [X0] : m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X0)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1639,f139])).

fof(f1639,plain,(
    ! [X3] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X3)))),X3) ),
    inference(superposition,[],[f1425,f907])).

fof(f1425,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),X0) ),
    inference(backward_demodulation,[],[f1398,f794])).

fof(f794,plain,(
    ! [X0,X1] : r1_tarski(k7_subset_1(X0,sK7(k1_zfmisc_1(X0)),X1),X0) ),
    inference(unit_resulting_resolution,[],[f742,f138])).

fof(f38123,plain,
    ( spl10_520
    | ~ spl10_394 ),
    inference(avatar_split_clause,[],[f28581,f28576,f38121])).

fof(f38121,plain,
    ( spl10_520
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_520])])).

fof(f28576,plain,
    ( spl10_394
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_394])])).

fof(f28581,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_394 ),
    inference(unit_resulting_resolution,[],[f28577,f139])).

fof(f28577,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),u1_struct_0(sK3))
    | ~ spl10_394 ),
    inference(avatar_component_clause,[],[f28576])).

fof(f38079,plain,
    ( spl10_392
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f37978,f27115,f28569])).

fof(f28569,plain,
    ( spl10_392
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_392])])).

fof(f37978,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3))
    | ~ spl10_332 ),
    inference(superposition,[],[f37943,f907])).

fof(f37943,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),X0),u1_struct_0(sK3))
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f27148,f138])).

fof(f27148,plain,
    ( ! [X2] : m1_subset_1(k6_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_332 ),
    inference(forward_demodulation,[],[f27139,f27131])).

fof(f27131,plain,
    ( ! [X0] : k6_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),X0) = k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),X0)
    | ~ spl10_332 ),
    inference(unit_resulting_resolution,[],[f27116,f155])).

fof(f27139,plain,
    ( ! [X2] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),X2),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_332 ),
    inference(resolution,[],[f27116,f142])).

fof(f38060,plain,
    ( spl10_324
    | spl10_229
    | ~ spl10_332 ),
    inference(avatar_split_clause,[],[f38032,f27115,f22415,f27011])).

fof(f27011,plain,
    ( spl10_324
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_324])])).

fof(f38032,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_332 ),
    inference(subsumption_resolution,[],[f36919,f22416])).

fof(f36919,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_332 ),
    inference(resolution,[],[f27116,f134])).

fof(f38036,plain,
    ( spl10_332
    | ~ spl10_300 ),
    inference(avatar_split_clause,[],[f25999,f25988,f27115])).

fof(f25988,plain,
    ( spl10_300
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_300])])).

fof(f25999,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_300 ),
    inference(resolution,[],[f25989,f139])).

fof(f25989,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),u1_struct_0(sK3))
    | ~ spl10_300 ),
    inference(avatar_component_clause,[],[f25988])).

fof(f38031,plain,
    ( spl10_229
    | ~ spl10_300
    | spl10_325 ),
    inference(avatar_contradiction_clause,[],[f38030])).

fof(f38030,plain,
    ( $false
    | ~ spl10_229
    | ~ spl10_300
    | ~ spl10_325 ),
    inference(subsumption_resolution,[],[f38029,f25999])).

fof(f38029,plain,
    ( ~ m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_325 ),
    inference(unit_resulting_resolution,[],[f22416,f27009,f134])).

fof(f27009,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_325 ),
    inference(avatar_component_clause,[],[f27008])).

fof(f27008,plain,
    ( spl10_325
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_325])])).

fof(f38028,plain,
    ( spl10_332
    | ~ spl10_324 ),
    inference(avatar_split_clause,[],[f36889,f27011,f27115])).

fof(f36889,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_324 ),
    inference(resolution,[],[f27012,f133])).

fof(f27012,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_324 ),
    inference(avatar_component_clause,[],[f27011])).

fof(f38027,plain,
    ( ~ spl10_332
    | spl10_393 ),
    inference(avatar_contradiction_clause,[],[f38026])).

fof(f38026,plain,
    ( $false
    | ~ spl10_332
    | ~ spl10_393 ),
    inference(subsumption_resolution,[],[f28567,f37978])).

fof(f28567,plain,
    ( ~ r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3))
    | ~ spl10_393 ),
    inference(avatar_component_clause,[],[f28566])).

fof(f28566,plain,
    ( spl10_393
  <=> ~ r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_393])])).

fof(f38025,plain,
    ( spl10_518
    | ~ spl10_392 ),
    inference(avatar_split_clause,[],[f28580,f28569,f38023])).

fof(f28580,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_392 ),
    inference(resolution,[],[f28570,f139])).

fof(f28570,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3))
    | ~ spl10_392 ),
    inference(avatar_component_clause,[],[f28569])).

fof(f37925,plain,
    ( ~ spl10_517
    | spl10_479 ),
    inference(avatar_split_clause,[],[f37739,f37064,f37923])).

fof(f37923,plain,
    ( spl10_517
  <=> ~ r2_hidden(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_517])])).

fof(f37064,plain,
    ( spl10_479
  <=> ~ m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_479])])).

fof(f37739,plain,
    ( ~ r2_hidden(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_479 ),
    inference(unit_resulting_resolution,[],[f225,f37065,f146])).

fof(f37065,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_479 ),
    inference(avatar_component_clause,[],[f37064])).

fof(f37736,plain,
    ( ~ spl10_479
    | spl10_381 ),
    inference(avatar_split_clause,[],[f37678,f28121,f37064])).

fof(f28121,plain,
    ( spl10_381
  <=> ~ r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_381])])).

fof(f37678,plain,
    ( ~ m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_381 ),
    inference(unit_resulting_resolution,[],[f28122,f138])).

fof(f28122,plain,
    ( ~ r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_381 ),
    inference(avatar_component_clause,[],[f28121])).

fof(f37685,plain,
    ( spl10_514
    | spl10_229
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f37615,f25372,f22415,f37683])).

fof(f37683,plain,
    ( spl10_514
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_514])])).

fof(f37615,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(superposition,[],[f37456,f907])).

fof(f37456,plain,
    ( ! [X3] : r2_hidden(k6_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),X3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(superposition,[],[f33541,f907])).

fof(f33541,plain,
    ( ! [X0,X1] : r2_hidden(k6_subset_1(k6_subset_1(k3_subset_1(sK5,sK5),X0),X1),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f22416,f26745,f134])).

fof(f37677,plain,
    ( spl10_478
    | ~ spl10_380 ),
    inference(avatar_split_clause,[],[f36963,f28124,f37067])).

fof(f37067,plain,
    ( spl10_478
  <=> m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_478])])).

fof(f28124,plain,
    ( spl10_380
  <=> r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_380])])).

fof(f36963,plain,
    ( m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_380 ),
    inference(resolution,[],[f28125,f139])).

fof(f28125,plain,
    ( r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_380 ),
    inference(avatar_component_clause,[],[f28124])).

fof(f37669,plain,
    ( ~ spl10_513
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28984,f25196,f37667])).

fof(f37667,plain,
    ( spl10_513
  <=> ~ r2_hidden(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_513])])).

fof(f28984,plain,
    ( ~ r2_hidden(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f3230])).

fof(f37662,plain,
    ( spl10_510
    | ~ spl10_384 ),
    inference(avatar_split_clause,[],[f28555,f28150,f37660])).

fof(f37660,plain,
    ( spl10_510
  <=> m1_subset_1(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_510])])).

fof(f28150,plain,
    ( spl10_384
  <=> r1_tarski(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_384])])).

fof(f28555,plain,
    ( m1_subset_1(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_384 ),
    inference(resolution,[],[f28151,f139])).

fof(f28151,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_384 ),
    inference(avatar_component_clause,[],[f28150])).

fof(f37655,plain,
    ( spl10_508
    | ~ spl10_498 ),
    inference(avatar_split_clause,[],[f37551,f37524,f37646])).

fof(f37646,plain,
    ( spl10_508
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_508])])).

fof(f37524,plain,
    ( spl10_498
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_498])])).

fof(f37551,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_498 ),
    inference(resolution,[],[f37525,f133])).

fof(f37525,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_498 ),
    inference(avatar_component_clause,[],[f37524])).

fof(f37652,plain,
    ( spl10_382
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f36958,f26052,f28143])).

fof(f28143,plain,
    ( spl10_382
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_382])])).

fof(f36958,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_304 ),
    inference(superposition,[],[f29601,f907])).

fof(f29601,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0),u1_struct_0(sK3))
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f26120,f138])).

fof(f26120,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_304 ),
    inference(forward_demodulation,[],[f26103,f26106])).

fof(f26106,plain,
    ( ! [X0] : k6_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0) = k7_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0)
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f26053,f155])).

fof(f26103,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f26053,f142])).

fof(f37650,plain,
    ( ~ spl10_304
    | spl10_383 ),
    inference(avatar_contradiction_clause,[],[f37649])).

fof(f37649,plain,
    ( $false
    | ~ spl10_304
    | ~ spl10_383 ),
    inference(subsumption_resolution,[],[f28141,f36958])).

fof(f28141,plain,
    ( ~ r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_383 ),
    inference(avatar_component_clause,[],[f28140])).

fof(f28140,plain,
    ( spl10_383
  <=> ~ r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_383])])).

fof(f37648,plain,
    ( spl10_508
    | ~ spl10_382 ),
    inference(avatar_split_clause,[],[f28553,f28143,f37646])).

fof(f28553,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_382 ),
    inference(resolution,[],[f28144,f139])).

fof(f28144,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_382 ),
    inference(avatar_component_clause,[],[f28143])).

fof(f37641,plain,
    ( ~ spl10_507
    | spl10_235
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f27073,f25372,f24775,f37639])).

fof(f37639,plain,
    ( spl10_507
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_507])])).

fof(f27073,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)))
    | ~ spl10_235
    | ~ spl10_262 ),
    inference(superposition,[],[f26722,f878])).

fof(f26722,plain,
    ( ! [X0] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k6_subset_1(k3_subset_1(sK5,sK5),X0))
    | ~ spl10_235
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f24776,f25402,f146])).

fof(f37602,plain,
    ( ~ spl10_505
    | ~ spl10_220
    | spl10_235 ),
    inference(avatar_split_clause,[],[f29668,f24775,f22353,f37600])).

fof(f37600,plain,
    ( spl10_505
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_505])])).

fof(f29668,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)))
    | ~ spl10_220
    | ~ spl10_235 ),
    inference(unit_resulting_resolution,[],[f24776,f22354,f146])).

fof(f37588,plain,
    ( ~ spl10_503
    | spl10_235
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f29560,f29552,f24775,f37586])).

fof(f37586,plain,
    ( spl10_503
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_503])])).

fof(f29560,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))
    | ~ spl10_235
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f24776,f29553,f146])).

fof(f37560,plain,
    ( ~ spl10_501
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28967,f25196,f37558])).

fof(f37558,plain,
    ( spl10_501
  <=> ~ r2_hidden(sK5,sK7(k1_zfmisc_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_501])])).

fof(f28967,plain,
    ( ~ r2_hidden(sK5,sK7(k1_zfmisc_1(k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f1860])).

fof(f1860,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK7(k1_zfmisc_1(k3_subset_1(X6,X6))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f1683,f146])).

fof(f37526,plain,
    ( spl10_498
    | spl10_229
    | ~ spl10_304 ),
    inference(avatar_split_clause,[],[f37369,f26052,f22415,f37524])).

fof(f37369,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_304 ),
    inference(superposition,[],[f29606,f907])).

fof(f29606,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_304 ),
    inference(unit_resulting_resolution,[],[f22416,f26120,f134])).

fof(f37512,plain,
    ( ~ spl10_497
    | spl10_265 ),
    inference(avatar_split_clause,[],[f37233,f25376,f37510])).

fof(f37510,plain,
    ( spl10_497
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_497])])).

fof(f25376,plain,
    ( spl10_265
  <=> ~ m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_265])])).

fof(f37233,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))))
    | ~ spl10_265 ),
    inference(unit_resulting_resolution,[],[f25377,f1813])).

fof(f1813,plain,(
    ! [X6,X5] :
      ( ~ r2_hidden(X5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X6)))))
      | m1_subset_1(X5,X6) ) ),
    inference(resolution,[],[f1660,f146])).

fof(f25377,plain,
    ( ~ m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_265 ),
    inference(avatar_component_clause,[],[f25376])).

fof(f37505,plain,
    ( spl10_494
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f515,f295,f37503])).

fof(f37503,plain,
    ( spl10_494
  <=> m1_subset_1(k3_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_494])])).

fof(f515,plain,
    ( m1_subset_1(k3_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f135])).

fof(f37443,plain,
    ( spl10_492
    | spl10_229
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f26935,f25372,f22415,f37441])).

fof(f37441,plain,
    ( spl10_492
  <=> r2_hidden(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_492])])).

fof(f26935,plain,
    ( r2_hidden(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(superposition,[],[f26725,f878])).

fof(f26725,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(k3_subset_1(sK5,sK5),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f22416,f25402,f134])).

fof(f37436,plain,
    ( spl10_490
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24704,f22415,f37434])).

fof(f37434,plain,
    ( spl10_490
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_490])])).

fof(f24704,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f1683,f22416,f134])).

fof(f37429,plain,
    ( ~ spl10_489
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24588,f22415,f37427])).

fof(f37427,plain,
    ( spl10_489
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_489])])).

fof(f24588,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f5324])).

fof(f5324,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X3),sK7(k1_zfmisc_1(k3_subset_1(X3,X3))))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f3574,f907])).

fof(f3574,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_zfmisc_1(X0),k6_subset_1(k3_subset_1(X0,X0),X1))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f3351,f878])).

fof(f3351,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X3),k6_subset_1(k6_subset_1(X3,X4),X5))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f1479,f132])).

fof(f1479,plain,(
    ! [X26,X27,X25] :
      ( r2_hidden(k6_subset_1(k6_subset_1(X25,X26),X27),k1_zfmisc_1(X25))
      | v1_xboole_0(k1_zfmisc_1(X25)) ) ),
    inference(backward_demodulation,[],[f1389,f784])).

fof(f784,plain,(
    ! [X26,X27,X25] :
      ( v1_xboole_0(k1_zfmisc_1(X25))
      | r2_hidden(k7_subset_1(X25,k6_subset_1(X25,X26),X27),k1_zfmisc_1(X25)) ) ),
    inference(resolution,[],[f740,f134])).

fof(f37379,plain,
    ( spl10_486
    | ~ spl10_220
    | spl10_229 ),
    inference(avatar_split_clause,[],[f29671,f22415,f22353,f37377])).

fof(f37377,plain,
    ( spl10_486
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_486])])).

fof(f29671,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_220
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f22354,f134])).

fof(f37356,plain,
    ( spl10_484
    | spl10_229
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f29563,f29552,f22415,f37354])).

fof(f37354,plain,
    ( spl10_484
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_484])])).

fof(f29563,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f22416,f29553,f134])).

fof(f37293,plain,
    ( ~ spl10_483
    | spl10_265 ),
    inference(avatar_split_clause,[],[f37220,f25376,f37291])).

fof(f37291,plain,
    ( spl10_483
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_483])])).

fof(f37220,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl10_265 ),
    inference(unit_resulting_resolution,[],[f25377,f577])).

fof(f577,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k3_subset_1(X3,X3))
      | m1_subset_1(X2,X3) ) ),
    inference(resolution,[],[f146,f513])).

fof(f37279,plain,
    ( ~ spl10_481
    | spl10_265 ),
    inference(avatar_split_clause,[],[f37224,f25376,f37277])).

fof(f37277,plain,
    ( spl10_481
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_481])])).

fof(f37224,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl10_265 ),
    inference(unit_resulting_resolution,[],[f25377,f583])).

fof(f583,plain,(
    ! [X15,X16] :
      ( ~ r2_hidden(X15,sK7(k1_zfmisc_1(X16)))
      | m1_subset_1(X15,X16) ) ),
    inference(resolution,[],[f146,f129])).

fof(f37264,plain,
    ( ~ spl10_269
    | spl10_265 ),
    inference(avatar_split_clause,[],[f37082,f25376,f25454])).

fof(f25454,plain,
    ( spl10_269
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_269])])).

fof(f37082,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_265 ),
    inference(unit_resulting_resolution,[],[f225,f25377,f146])).

fof(f37262,plain,
    ( ~ spl10_253
    | spl10_265 ),
    inference(avatar_split_clause,[],[f37080,f25376,f25320])).

fof(f25320,plain,
    ( spl10_253
  <=> ~ r1_tarski(sK7(k1_zfmisc_1(sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_253])])).

fof(f37080,plain,
    ( ~ r1_tarski(sK7(k1_zfmisc_1(sK5)),u1_struct_0(sK3))
    | ~ spl10_265 ),
    inference(unit_resulting_resolution,[],[f25377,f139])).

fof(f37079,plain,
    ( ~ spl10_252
    | spl10_265 ),
    inference(avatar_contradiction_clause,[],[f37078])).

fof(f37078,plain,
    ( $false
    | ~ spl10_252
    | ~ spl10_265 ),
    inference(subsumption_resolution,[],[f36439,f25377])).

fof(f36439,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_252 ),
    inference(resolution,[],[f25324,f139])).

fof(f25324,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK5)),u1_struct_0(sK3))
    | ~ spl10_252 ),
    inference(avatar_component_clause,[],[f25323])).

fof(f25323,plain,
    ( spl10_252
  <=> r1_tarski(sK7(k1_zfmisc_1(sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_252])])).

fof(f37077,plain,
    ( ~ spl10_252
    | spl10_265 ),
    inference(avatar_contradiction_clause,[],[f37076])).

fof(f37076,plain,
    ( $false
    | ~ spl10_252
    | ~ spl10_265 ),
    inference(subsumption_resolution,[],[f36438,f25377])).

fof(f36438,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_252 ),
    inference(unit_resulting_resolution,[],[f25324,f139])).

fof(f37075,plain,
    ( ~ spl10_252
    | spl10_265 ),
    inference(avatar_contradiction_clause,[],[f37074])).

fof(f37074,plain,
    ( $false
    | ~ spl10_252
    | ~ spl10_265 ),
    inference(subsumption_resolution,[],[f25328,f25377])).

fof(f25328,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_252 ),
    inference(unit_resulting_resolution,[],[f25324,f139])).

fof(f37073,plain,
    ( ~ spl10_252
    | spl10_265 ),
    inference(avatar_contradiction_clause,[],[f37072])).

fof(f37072,plain,
    ( $false
    | ~ spl10_252
    | ~ spl10_265 ),
    inference(subsumption_resolution,[],[f25329,f25377])).

fof(f25329,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_252 ),
    inference(resolution,[],[f25324,f139])).

fof(f37071,plain,
    ( spl10_265
    | ~ spl10_268 ),
    inference(avatar_contradiction_clause,[],[f37070])).

fof(f37070,plain,
    ( $false
    | ~ spl10_265
    | ~ spl10_268 ),
    inference(subsumption_resolution,[],[f25377,f36517])).

fof(f36517,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_268 ),
    inference(resolution,[],[f25458,f133])).

fof(f25458,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_268 ),
    inference(avatar_component_clause,[],[f25457])).

fof(f25457,plain,
    ( spl10_268
  <=> r2_hidden(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_268])])).

fof(f37069,plain,
    ( spl10_478
    | ~ spl10_264 ),
    inference(avatar_split_clause,[],[f26774,f25379,f37067])).

fof(f25379,plain,
    ( spl10_264
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_264])])).

fof(f26774,plain,
    ( m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_264 ),
    inference(superposition,[],[f25426,f878])).

fof(f25426,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(sK7(k1_zfmisc_1(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_264 ),
    inference(forward_demodulation,[],[f25409,f25412])).

fof(f25412,plain,
    ( ! [X0] : k6_subset_1(sK7(k1_zfmisc_1(sK5)),X0) = k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5)),X0)
    | ~ spl10_264 ),
    inference(unit_resulting_resolution,[],[f25380,f155])).

fof(f25380,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_264 ),
    inference(avatar_component_clause,[],[f25379])).

fof(f25409,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5)),X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_264 ),
    inference(unit_resulting_resolution,[],[f25380,f142])).

fof(f36758,plain,
    ( spl10_476
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36437,f33608,f36756])).

fof(f36756,plain,
    ( spl10_476
  <=> r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),sK7(k1_zfmisc_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_476])])).

fof(f33608,plain,
    ( spl10_459
  <=> ~ v1_xboole_0(sK7(k1_zfmisc_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_459])])).

fof(f36437,plain,
    ( r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f129,f33609,f134])).

fof(f33609,plain,
    ( ~ v1_xboole_0(sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_459 ),
    inference(avatar_component_clause,[],[f33608])).

fof(f36751,plain,
    ( ~ spl10_475
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36435,f33608,f36749])).

fof(f36749,plain,
    ( spl10_475
  <=> ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_475])])).

fof(f36435,plain,
    ( ~ r2_hidden(sK7(k1_zfmisc_1(sK5)),sK7(sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f33609,f363])).

fof(f36552,plain,
    ( ~ spl10_473
    | spl10_273
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36538,f33608,f25496,f36550])).

fof(f25496,plain,
    ( spl10_273
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_273])])).

fof(f36538,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_273
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f33609,f25497,f134])).

fof(f25497,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_273 ),
    inference(avatar_component_clause,[],[f25496])).

fof(f36545,plain,
    ( ~ spl10_471
    | ~ spl10_468 ),
    inference(avatar_split_clause,[],[f36533,f36526,f36543])).

fof(f36543,plain,
    ( spl10_471
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_471])])).

fof(f36526,plain,
    ( spl10_468
  <=> r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_468])])).

fof(f36533,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_468 ),
    inference(unit_resulting_resolution,[],[f36527,f132])).

fof(f36527,plain,
    ( r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_468 ),
    inference(avatar_component_clause,[],[f36526])).

fof(f36528,plain,
    ( spl10_468
    | spl10_37
    | ~ spl10_460 ),
    inference(avatar_split_clause,[],[f36520,f33617,f318,f36526])).

fof(f33617,plain,
    ( spl10_460
  <=> m1_subset_1(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_460])])).

fof(f36520,plain,
    ( r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_460 ),
    inference(unit_resulting_resolution,[],[f319,f33618,f134])).

fof(f33618,plain,
    ( m1_subset_1(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_460 ),
    inference(avatar_component_clause,[],[f33617])).

fof(f36460,plain,
    ( spl10_466
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36433,f33608,f36458])).

fof(f36458,plain,
    ( spl10_466
  <=> m1_subset_1(sK7(sK7(k1_zfmisc_1(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_466])])).

fof(f36433,plain,
    ( m1_subset_1(sK7(sK7(k1_zfmisc_1(sK5))),sK5)
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f33609,f587])).

fof(f587,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(sK7(k1_zfmisc_1(X0))),X0)
      | v1_xboole_0(sK7(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f583,f360])).

fof(f36453,plain,
    ( spl10_464
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36432,f33608,f36451])).

fof(f36451,plain,
    ( spl10_464
  <=> r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_464])])).

fof(f36432,plain,
    ( r2_hidden(sK7(sK7(k1_zfmisc_1(sK5))),sK5)
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f33609,f677])).

fof(f677,plain,(
    ! [X9] :
      ( r2_hidden(sK7(sK7(k1_zfmisc_1(X9))),X9)
      | v1_xboole_0(sK7(k1_zfmisc_1(X9))) ) ),
    inference(subsumption_resolution,[],[f676,f492])).

fof(f492,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(sK7(k1_zfmisc_1(X0))) ) ),
    inference(resolution,[],[f488,f360])).

fof(f488,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,sK7(k1_zfmisc_1(X6)))
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f147,f129])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t5_subset)).

fof(f676,plain,(
    ! [X9] :
      ( v1_xboole_0(sK7(k1_zfmisc_1(X9)))
      | v1_xboole_0(X9)
      | r2_hidden(sK7(sK7(k1_zfmisc_1(X9))),X9) ) ),
    inference(resolution,[],[f587,f134])).

fof(f36446,plain,
    ( ~ spl10_463
    | spl10_459 ),
    inference(avatar_split_clause,[],[f36431,f33608,f36444])).

fof(f36444,plain,
    ( spl10_463
  <=> ~ r2_hidden(sK5,sK7(sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_463])])).

fof(f36431,plain,
    ( ~ r2_hidden(sK5,sK7(sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_459 ),
    inference(unit_resulting_resolution,[],[f33609,f697])).

fof(f697,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK7(sK7(k1_zfmisc_1(X1))))
      | v1_xboole_0(sK7(k1_zfmisc_1(X1))) ) ),
    inference(resolution,[],[f677,f132])).

fof(f36430,plain,
    ( spl10_44
    | ~ spl10_458 ),
    inference(avatar_split_clause,[],[f34346,f33611,f393])).

fof(f33611,plain,
    ( spl10_458
  <=> v1_xboole_0(sK7(k1_zfmisc_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_458])])).

fof(f34346,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_458 ),
    inference(backward_demodulation,[],[f33620,f33612])).

fof(f33612,plain,
    ( v1_xboole_0(sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_458 ),
    inference(avatar_component_clause,[],[f33611])).

fof(f33620,plain,
    ( k1_xboole_0 = sK7(k1_zfmisc_1(sK5))
    | ~ spl10_458 ),
    inference(unit_resulting_resolution,[],[f33612,f112])).

fof(f33619,plain,
    ( spl10_458
    | spl10_460
    | ~ spl10_264 ),
    inference(avatar_split_clause,[],[f26750,f25379,f33617,f33611])).

fof(f26750,plain,
    ( m1_subset_1(sK7(sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | v1_xboole_0(sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_264 ),
    inference(resolution,[],[f25421,f360])).

fof(f25421,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK7(k1_zfmisc_1(sK5)))
        | m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl10_264 ),
    inference(resolution,[],[f25380,f146])).

fof(f33276,plain,
    ( spl10_456
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32560,f29838,f33274])).

fof(f33274,plain,
    ( spl10_456
  <=> r2_hidden(sK7(k3_subset_1(sK5,sK5)),k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_456])])).

fof(f29838,plain,
    ( spl10_429
  <=> ~ v1_xboole_0(k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_429])])).

fof(f32560,plain,
    ( r2_hidden(sK7(k3_subset_1(sK5,sK5)),k3_subset_1(sK5,sK5))
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f129,f29839,f134])).

fof(f29839,plain,
    ( ~ v1_xboole_0(k3_subset_1(sK5,sK5))
    | ~ spl10_429 ),
    inference(avatar_component_clause,[],[f29838])).

fof(f33269,plain,
    ( ~ spl10_455
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32558,f29838,f33267])).

fof(f33267,plain,
    ( spl10_455
  <=> ~ r2_hidden(k3_subset_1(sK5,sK5),sK7(k3_subset_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_455])])).

fof(f32558,plain,
    ( ~ r2_hidden(k3_subset_1(sK5,sK5),sK7(k3_subset_1(sK5,sK5)))
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f363])).

fof(f32906,plain,
    ( ~ spl10_453
    | spl10_271
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32892,f29838,f25489,f32904])).

fof(f32904,plain,
    ( spl10_453
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_453])])).

fof(f25489,plain,
    ( spl10_271
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_271])])).

fof(f32892,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK5))
    | ~ spl10_271
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f25490,f134])).

fof(f25490,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK5))
    | ~ spl10_271 ),
    inference(avatar_component_clause,[],[f25489])).

fof(f32899,plain,
    ( ~ spl10_451
    | ~ spl10_448 ),
    inference(avatar_split_clause,[],[f32887,f32880,f32897])).

fof(f32897,plain,
    ( spl10_451
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(k3_subset_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_451])])).

fof(f32880,plain,
    ( spl10_448
  <=> r2_hidden(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_448])])).

fof(f32887,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(k3_subset_1(sK5,sK5)))
    | ~ spl10_448 ),
    inference(unit_resulting_resolution,[],[f32881,f132])).

fof(f32881,plain,
    ( r2_hidden(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_448 ),
    inference(avatar_component_clause,[],[f32880])).

fof(f32882,plain,
    ( spl10_448
    | spl10_37
    | ~ spl10_430 ),
    inference(avatar_split_clause,[],[f32874,f29847,f318,f32880])).

fof(f29847,plain,
    ( spl10_430
  <=> m1_subset_1(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_430])])).

fof(f32874,plain,
    ( r2_hidden(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_430 ),
    inference(unit_resulting_resolution,[],[f319,f29848,f134])).

fof(f29848,plain,
    ( m1_subset_1(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_430 ),
    inference(avatar_component_clause,[],[f29847])).

fof(f32854,plain,
    ( ~ spl10_447
    | ~ spl10_2
    | spl10_445 ),
    inference(avatar_split_clause,[],[f32847,f32841,f167,f32852])).

fof(f32852,plain,
    ( spl10_447
  <=> ~ v4_pre_topc(u1_struct_0(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_447])])).

fof(f32847,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK3),sK3)
    | ~ spl10_2
    | ~ spl10_445 ),
    inference(forward_demodulation,[],[f32846,f628])).

fof(f32846,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))),sK3)
    | ~ spl10_2
    | ~ spl10_445 ),
    inference(unit_resulting_resolution,[],[f168,f513,f32842,f126])).

fof(f32843,plain,
    ( ~ spl10_445
    | ~ spl10_4
    | spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_400
    | spl10_417 ),
    inference(avatar_split_clause,[],[f32553,f29735,f29016,f479,f295,f231,f174,f32841])).

fof(f32553,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_400
    | ~ spl10_417 ),
    inference(subsumption_resolution,[],[f29219,f29736])).

fof(f29219,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | ~ spl10_4
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_400 ),
    inference(backward_demodulation,[],[f29133,f5143])).

fof(f5143,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | v3_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))),sK2)
    | ~ spl10_19
    | ~ spl10_30 ),
    inference(resolution,[],[f3734,f513])).

fof(f32810,plain,
    ( ~ spl10_443
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32554,f29838,f32808])).

fof(f32808,plain,
    ( spl10_443
  <=> ~ r2_hidden(sK5,sK7(k3_subset_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_443])])).

fof(f32554,plain,
    ( ~ r2_hidden(sK5,sK7(k3_subset_1(sK5,sK5)))
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f723])).

fof(f723,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK7(k3_subset_1(X1,X1)))
      | v1_xboole_0(k3_subset_1(X1,X1)) ) ),
    inference(resolution,[],[f717,f132])).

fof(f717,plain,(
    ! [X9] :
      ( r2_hidden(sK7(k3_subset_1(X9,X9)),X9)
      | v1_xboole_0(k3_subset_1(X9,X9)) ) ),
    inference(subsumption_resolution,[],[f716,f531])).

fof(f531,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k3_subset_1(X0,X0)) ) ),
    inference(resolution,[],[f525,f360])).

fof(f525,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,k3_subset_1(X1,X1))
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f513,f147])).

fof(f716,plain,(
    ! [X9] :
      ( v1_xboole_0(k3_subset_1(X9,X9))
      | v1_xboole_0(X9)
      | r2_hidden(sK7(k3_subset_1(X9,X9)),X9) ) ),
    inference(resolution,[],[f588,f134])).

fof(f588,plain,(
    ! [X0] :
      ( m1_subset_1(sK7(k3_subset_1(X0,X0)),X0)
      | v1_xboole_0(k3_subset_1(X0,X0)) ) ),
    inference(resolution,[],[f577,f360])).

fof(f32792,plain,
    ( spl10_440
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32556,f29838,f32790])).

fof(f32790,plain,
    ( spl10_440
  <=> m1_subset_1(sK7(k3_subset_1(sK5,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_440])])).

fof(f32556,plain,
    ( m1_subset_1(sK7(k3_subset_1(sK5,sK5)),sK5)
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f588])).

fof(f32785,plain,
    ( spl10_438
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32555,f29838,f32783])).

fof(f32783,plain,
    ( spl10_438
  <=> r2_hidden(sK7(k3_subset_1(sK5,sK5)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_438])])).

fof(f32555,plain,
    ( r2_hidden(sK7(k3_subset_1(sK5,sK5)),sK5)
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f717])).

fof(f32595,plain,
    ( ~ spl10_437
    | spl10_247
    | spl10_255 ),
    inference(avatar_split_clause,[],[f32564,f25331,f25255,f32593])).

fof(f25255,plain,
    ( spl10_247
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_247])])).

fof(f25331,plain,
    ( spl10_255
  <=> ~ v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_255])])).

fof(f32564,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK5)
    | ~ spl10_247
    | ~ spl10_255 ),
    inference(unit_resulting_resolution,[],[f25256,f25332,f134])).

fof(f25332,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl10_255 ),
    inference(avatar_component_clause,[],[f25331])).

fof(f25256,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK5)
    | ~ spl10_247 ),
    inference(avatar_component_clause,[],[f25255])).

fof(f32579,plain,
    ( spl10_434
    | spl10_255 ),
    inference(avatar_split_clause,[],[f32565,f25331,f32577])).

fof(f32577,plain,
    ( spl10_434
  <=> r2_hidden(sK7(sK5),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_434])])).

fof(f32565,plain,
    ( r2_hidden(sK7(sK5),sK5)
    | ~ spl10_255 ),
    inference(unit_resulting_resolution,[],[f129,f25332,f134])).

fof(f32572,plain,
    ( ~ spl10_433
    | spl10_255 ),
    inference(avatar_split_clause,[],[f32562,f25331,f32570])).

fof(f32570,plain,
    ( spl10_433
  <=> ~ r2_hidden(sK5,sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_433])])).

fof(f32562,plain,
    ( ~ r2_hidden(sK5,sK7(sK5))
    | ~ spl10_255 ),
    inference(unit_resulting_resolution,[],[f25332,f363])).

fof(f32561,plain,
    ( ~ spl10_255
    | spl10_429 ),
    inference(avatar_split_clause,[],[f32557,f29838,f25331])).

fof(f32557,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ spl10_429 ),
    inference(unit_resulting_resolution,[],[f29839,f531])).

fof(f32552,plain,
    ( spl10_44
    | ~ spl10_428 ),
    inference(avatar_split_clause,[],[f30513,f29841,f393])).

fof(f29841,plain,
    ( spl10_428
  <=> v1_xboole_0(k3_subset_1(sK5,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_428])])).

fof(f30513,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_428 ),
    inference(backward_demodulation,[],[f29850,f29842])).

fof(f29842,plain,
    ( v1_xboole_0(k3_subset_1(sK5,sK5))
    | ~ spl10_428 ),
    inference(avatar_component_clause,[],[f29841])).

fof(f29850,plain,
    ( k1_xboole_0 = k3_subset_1(sK5,sK5)
    | ~ spl10_428 ),
    inference(unit_resulting_resolution,[],[f29842,f112])).

fof(f29849,plain,
    ( spl10_428
    | spl10_430
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f26714,f25372,f29847,f29841])).

fof(f26714,plain,
    ( m1_subset_1(sK7(k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | v1_xboole_0(k3_subset_1(sK5,sK5))
    | ~ spl10_262 ),
    inference(resolution,[],[f25397,f360])).

fof(f25397,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k3_subset_1(sK5,sK5))
        | m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl10_262 ),
    inference(resolution,[],[f25373,f146])).

fof(f29820,plain,
    ( spl10_426
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24630,f22415,f29818])).

fof(f29818,plain,
    ( spl10_426
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_426])])).

fof(f24630,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f516,f22416,f134])).

fof(f29787,plain,
    ( ~ spl10_425
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24545,f22415,f29785])).

fof(f29785,plain,
    ( spl10_425
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_425])])).

fof(f24545,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f1044])).

fof(f1044,plain,(
    ! [X5] :
      ( ~ r2_hidden(k1_zfmisc_1(X5),k3_subset_1(X5,sK7(k1_zfmisc_1(X5))))
      | v1_xboole_0(k1_zfmisc_1(X5)) ) ),
    inference(superposition,[],[f507,f890])).

fof(f507,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X2),k6_subset_1(X2,X3))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f358,f132])).

fof(f358,plain,(
    ! [X2,X1] :
      ( r2_hidden(k6_subset_1(X1,X2),k1_zfmisc_1(X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f134,f130])).

fof(f29766,plain,
    ( ~ spl10_423
    | ~ spl10_0
    | spl10_421 ),
    inference(avatar_split_clause,[],[f29765,f29755,f160,f29758])).

fof(f29755,plain,
    ( spl10_421
  <=> ~ v3_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_421])])).

fof(f29765,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ spl10_0
    | ~ spl10_421 ),
    inference(unit_resulting_resolution,[],[f161,f225,f29756,f126])).

fof(f29756,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl10_421 ),
    inference(avatar_component_clause,[],[f29755])).

fof(f29763,plain,
    ( ~ spl10_421
    | spl10_422
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(avatar_split_clause,[],[f29214,f29016,f295,f160,f29761,f29755])).

fof(f29761,plain,
    ( spl10_422
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_422])])).

fof(f29214,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f29087,f29017])).

fof(f29087,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK2),sK2)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,u1_struct_0(sK3))),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(superposition,[],[f8673,f29017])).

fof(f8673,plain,
    ( ! [X168] :
        ( ~ v3_pre_topc(k10_relat_1(sK4,X168),sK2)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X168)),sK2) )
    | ~ spl10_0
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f8605,f161])).

fof(f8605,plain,
    ( ! [X168] :
        ( ~ v3_pre_topc(k10_relat_1(sK4,X168),sK2)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X168)),sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_30 ),
    inference(resolution,[],[f125,f3735])).

fof(f29748,plain,
    ( ~ spl10_419
    | ~ spl10_0
    | spl10_417 ),
    inference(avatar_split_clause,[],[f29747,f29735,f160,f29738])).

fof(f29738,plain,
    ( spl10_419
  <=> ~ v4_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_419])])).

fof(f29747,plain,
    ( ~ v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ spl10_0
    | ~ spl10_417 ),
    inference(forward_demodulation,[],[f29746,f628])).

fof(f29746,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))),sK2)
    | ~ spl10_0
    | ~ spl10_417 ),
    inference(unit_resulting_resolution,[],[f161,f513,f29736,f126])).

fof(f29743,plain,
    ( ~ spl10_417
    | spl10_418
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(avatar_split_clause,[],[f29213,f29016,f295,f160,f29741,f29735])).

fof(f29741,plain,
    ( spl10_418
  <=> v4_pre_topc(u1_struct_0(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_418])])).

fof(f29213,plain,
    ( v4_pre_topc(u1_struct_0(sK2),sK2)
    | ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(forward_demodulation,[],[f29086,f29017])).

fof(f29086,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),sK2)
    | v4_pre_topc(k10_relat_1(sK4,u1_struct_0(sK3)),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_400 ),
    inference(superposition,[],[f8653,f29017])).

fof(f8653,plain,
    ( ! [X41] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X41)),sK2)
        | v4_pre_topc(k10_relat_1(sK4,X41),sK2) )
    | ~ spl10_0
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f8652,f3737])).

fof(f8652,plain,
    ( ! [X41] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X41)),sK2)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X41))),sK2) )
    | ~ spl10_0
    | ~ spl10_30 ),
    inference(subsumption_resolution,[],[f8555,f161])).

fof(f8555,plain,
    ( ! [X41] :
        ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X41)),sK2)
        | v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,X41))),sK2)
        | ~ l1_pre_topc(sK2) )
    | ~ spl10_30 ),
    inference(resolution,[],[f125,f3736])).

fof(f29655,plain,
    ( ~ spl10_415
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28954,f25196,f29653])).

fof(f29653,plain,
    ( spl10_415
  <=> ~ r2_hidden(sK5,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_415])])).

fof(f28954,plain,
    ( ~ r2_hidden(sK5,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f580])).

fof(f580,plain,(
    ! [X10,X9] :
      ( ~ r2_hidden(X9,k3_subset_1(X10,sK7(k1_zfmisc_1(X10))))
      | m1_subset_1(X9,X10) ) ),
    inference(resolution,[],[f146,f516])).

fof(f29591,plain,
    ( spl10_412
    | ~ spl10_410 ),
    inference(avatar_split_clause,[],[f29558,f29552,f29589])).

fof(f29589,plain,
    ( spl10_412
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_412])])).

fof(f29558,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),u1_struct_0(sK3))
    | ~ spl10_410 ),
    inference(unit_resulting_resolution,[],[f29553,f138])).

fof(f29554,plain,
    ( spl10_410
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25508,f25503,f29552])).

fof(f25508,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25504,f135])).

fof(f29446,plain,
    ( ~ spl10_409
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28965,f25196,f29444])).

fof(f29444,plain,
    ( spl10_409
  <=> ~ r2_hidden(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_409])])).

fof(f28965,plain,
    ( ~ r2_hidden(sK5,sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f1813])).

fof(f29398,plain,
    ( ~ spl10_407
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28952,f25196,f29396])).

fof(f29396,plain,
    ( spl10_407
  <=> ~ r2_hidden(sK5,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_407])])).

fof(f28952,plain,
    ( ~ r2_hidden(sK5,k3_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f577])).

fof(f29326,plain,
    ( ~ spl10_405
    | ~ spl10_2
    | ~ spl10_274
    | spl10_295 ),
    inference(avatar_split_clause,[],[f25655,f25640,f25503,f167,f29324])).

fof(f29324,plain,
    ( spl10_405
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_405])])).

fof(f25640,plain,
    ( spl10_295
  <=> ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_295])])).

fof(f25655,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),sK3)
    | ~ spl10_2
    | ~ spl10_274
    | ~ spl10_295 ),
    inference(unit_resulting_resolution,[],[f168,f25504,f25641,f126])).

fof(f25641,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ spl10_295 ),
    inference(avatar_component_clause,[],[f25640])).

fof(f29319,plain,
    ( ~ spl10_403
    | ~ spl10_226 ),
    inference(avatar_split_clause,[],[f29266,f22412,f29317])).

fof(f29317,plain,
    ( spl10_403
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK6(sK2,sK4,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_403])])).

fof(f22412,plain,
    ( spl10_226
  <=> r2_hidden(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_226])])).

fof(f29266,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK6(sK2,sK4,sK3))
    | ~ spl10_226 ),
    inference(unit_resulting_resolution,[],[f22413,f132])).

fof(f22413,plain,
    ( r2_hidden(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_226 ),
    inference(avatar_component_clause,[],[f22412])).

fof(f29259,plain,
    ( spl10_210
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22305,f22231,f22222])).

fof(f22222,plain,
    ( spl10_210
  <=> r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_210])])).

fof(f22305,plain,
    ( r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(superposition,[],[f22273,f910])).

fof(f29231,plain,
    ( spl10_262
    | ~ spl10_250 ),
    inference(avatar_split_clause,[],[f25327,f25316,f25372])).

fof(f25316,plain,
    ( spl10_250
  <=> r1_tarski(k3_subset_1(sK5,sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_250])])).

fof(f25327,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_250 ),
    inference(resolution,[],[f25317,f139])).

fof(f25317,plain,
    ( r1_tarski(k3_subset_1(sK5,sK5),u1_struct_0(sK3))
    | ~ spl10_250 ),
    inference(avatar_component_clause,[],[f25316])).

fof(f29018,plain,
    ( spl10_400
    | ~ spl10_30
    | ~ spl10_396 ),
    inference(avatar_split_clause,[],[f28590,f28587,f295,f29016])).

fof(f28587,plain,
    ( spl10_396
  <=> u1_struct_0(sK2) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_396])])).

fof(f28590,plain,
    ( u1_struct_0(sK2) = k10_relat_1(sK4,u1_struct_0(sK3))
    | ~ spl10_30
    | ~ spl10_396 ),
    inference(superposition,[],[f28588,f3662])).

fof(f28588,plain,
    ( u1_struct_0(sK2) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3))
    | ~ spl10_396 ),
    inference(avatar_component_clause,[],[f28587])).

fof(f29011,plain,
    ( ~ spl10_399
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28956,f25196,f29009])).

fof(f29009,plain,
    ( spl10_399
  <=> ~ r2_hidden(sK5,sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_399])])).

fof(f28956,plain,
    ( ~ r2_hidden(sK5,sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f583])).

fof(f28996,plain,
    ( ~ spl10_245
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28814,f25196,f25236])).

fof(f25236,plain,
    ( spl10_245
  <=> ~ r2_hidden(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_245])])).

fof(f28814,plain,
    ( ~ r2_hidden(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f225,f25197,f146])).

fof(f28994,plain,
    ( ~ spl10_243
    | spl10_241 ),
    inference(avatar_split_clause,[],[f28812,f25196,f25227])).

fof(f25227,plain,
    ( spl10_243
  <=> ~ r1_tarski(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_243])])).

fof(f28812,plain,
    ( ~ r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl10_241 ),
    inference(unit_resulting_resolution,[],[f25197,f139])).

fof(f28810,plain,
    ( ~ spl10_19
    | spl10_149
    | ~ spl10_206 ),
    inference(avatar_split_clause,[],[f22205,f22198,f6699,f231])).

fof(f28792,plain,
    ( spl10_241
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(avatar_contradiction_clause,[],[f28791])).

fof(f28791,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(subsumption_resolution,[],[f28754,f25197])).

fof(f28754,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(forward_demodulation,[],[f25519,f25630])).

fof(f25630,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5
    | ~ spl10_290 ),
    inference(avatar_component_clause,[],[f25629])).

fof(f25629,plain,
    ( spl10_290
  <=> k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_290])])).

fof(f25519,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274 ),
    inference(resolution,[],[f25504,f135])).

fof(f28790,plain,
    ( spl10_241
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(avatar_contradiction_clause,[],[f28789])).

fof(f28789,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(subsumption_resolution,[],[f28755,f25197])).

fof(f28755,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_274
    | ~ spl10_290 ),
    inference(forward_demodulation,[],[f25508,f25630])).

fof(f28787,plain,
    ( spl10_241
    | ~ spl10_244 ),
    inference(avatar_contradiction_clause,[],[f28786])).

fof(f28786,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_244 ),
    inference(subsumption_resolution,[],[f25248,f25197])).

fof(f25248,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_244 ),
    inference(resolution,[],[f25240,f133])).

fof(f25240,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_244 ),
    inference(avatar_component_clause,[],[f25239])).

fof(f25239,plain,
    ( spl10_244
  <=> r2_hidden(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_244])])).

fof(f28785,plain,
    ( spl10_241
    | ~ spl10_244 ),
    inference(avatar_contradiction_clause,[],[f28784])).

fof(f28784,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_244 ),
    inference(subsumption_resolution,[],[f25242,f25197])).

fof(f25242,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_244 ),
    inference(unit_resulting_resolution,[],[f225,f25240,f146])).

fof(f28783,plain,
    ( spl10_241
    | ~ spl10_244 ),
    inference(avatar_contradiction_clause,[],[f28782])).

fof(f28782,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_244 ),
    inference(subsumption_resolution,[],[f25244,f25197])).

fof(f25244,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_244 ),
    inference(unit_resulting_resolution,[],[f25240,f133])).

fof(f28781,plain,
    ( spl10_241
    | ~ spl10_242 ),
    inference(avatar_contradiction_clause,[],[f28780])).

fof(f28780,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_242 ),
    inference(subsumption_resolution,[],[f25234,f25197])).

fof(f25234,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_242 ),
    inference(resolution,[],[f25231,f139])).

fof(f25231,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl10_242 ),
    inference(avatar_component_clause,[],[f25230])).

fof(f25230,plain,
    ( spl10_242
  <=> r1_tarski(sK5,u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_242])])).

fof(f28779,plain,
    ( spl10_241
    | ~ spl10_242 ),
    inference(avatar_contradiction_clause,[],[f28778])).

fof(f28778,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_242 ),
    inference(subsumption_resolution,[],[f25233,f25197])).

fof(f25233,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_242 ),
    inference(unit_resulting_resolution,[],[f25231,f139])).

fof(f28776,plain,
    ( spl10_241
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_contradiction_clause,[],[f28775])).

fof(f28775,plain,
    ( $false
    | ~ spl10_241
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(subsumption_resolution,[],[f25197,f25864])).

fof(f25864,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25666,f25630])).

fof(f25666,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_292 ),
    inference(superposition,[],[f514,f25637])).

fof(f25637,plain,
    ( k3_subset_1(u1_struct_0(sK3),sK5) = k6_subset_1(u1_struct_0(sK3),sK5)
    | ~ spl10_292 ),
    inference(avatar_component_clause,[],[f25636])).

fof(f25636,plain,
    ( spl10_292
  <=> k3_subset_1(u1_struct_0(sK3),sK5) = k6_subset_1(u1_struct_0(sK3),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_292])])).

fof(f514,plain,(
    ! [X0,X1] : m1_subset_1(k3_subset_1(X0,k6_subset_1(X0,X1)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f130,f135])).

fof(f28750,plain,
    ( ~ spl10_18
    | spl10_149
    | ~ spl10_206 ),
    inference(avatar_contradiction_clause,[],[f28749])).

fof(f28749,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_149
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f6700,f24534])).

fof(f24534,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl10_18
    | ~ spl10_206 ),
    inference(unit_resulting_resolution,[],[f22199,f229,f118])).

fof(f229,plain,
    ( v5_pre_topc(sK4,sK2,sK3)
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_18
  <=> v5_pre_topc(sK4,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f28747,plain,
    ( ~ spl10_18
    | spl10_149
    | ~ spl10_206 ),
    inference(avatar_contradiction_clause,[],[f28746])).

fof(f28746,plain,
    ( $false
    | ~ spl10_18
    | ~ spl10_149
    | ~ spl10_206 ),
    inference(subsumption_resolution,[],[f22205,f229])).

fof(f28739,plain,
    ( ~ spl10_0
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | spl10_287
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(avatar_contradiction_clause,[],[f28738])).

fof(f28738,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | ~ spl10_287
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(subsumption_resolution,[],[f28737,f25610])).

fof(f25610,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK4,sK5),sK2)
    | ~ spl10_287 ),
    inference(avatar_component_clause,[],[f25609])).

fof(f25609,plain,
    ( spl10_287
  <=> ~ v3_pre_topc(k10_relat_1(sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_287])])).

fof(f28737,plain,
    ( v3_pre_topc(k10_relat_1(sK4,sK5),sK2)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(forward_demodulation,[],[f28734,f3737])).

fof(f28734,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5))),sK2)
    | ~ spl10_0
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(backward_demodulation,[],[f28633,f25580])).

fof(f25580,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5))),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_280 ),
    inference(unit_resulting_resolution,[],[f161,f3735,f25575,f127])).

fof(f25575,plain,
    ( v4_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5)),sK2)
    | ~ spl10_280 ),
    inference(avatar_component_clause,[],[f25574])).

fof(f25574,plain,
    ( spl10_280
  <=> v4_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_280])])).

fof(f28633,plain,
    ( k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5)) = k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(backward_demodulation,[],[f28590,f26817])).

fof(f26817,plain,
    ( k3_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,sK5)) = k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292
    | ~ spl10_310 ),
    inference(forward_demodulation,[],[f26816,f25637])).

fof(f26816,plain,
    ( k3_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,sK5)) = k10_relat_1(sK4,k6_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_310 ),
    inference(forward_demodulation,[],[f26805,f16903])).

fof(f26805,plain,
    ( k3_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,sK5)) = k6_subset_1(k10_relat_1(sK4,u1_struct_0(sK3)),k10_relat_1(sK4,sK5))
    | ~ spl10_310 ),
    inference(unit_resulting_resolution,[],[f26797,f154])).

fof(f26797,plain,
    ( m1_subset_1(k10_relat_1(sK4,sK5),k1_zfmisc_1(k10_relat_1(sK4,u1_struct_0(sK3))))
    | ~ spl10_310 ),
    inference(avatar_component_clause,[],[f26796])).

fof(f26796,plain,
    ( spl10_310
  <=> m1_subset_1(k10_relat_1(sK4,sK5),k1_zfmisc_1(k10_relat_1(sK4,u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_310])])).

fof(f28736,plain,
    ( ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | spl10_289
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(avatar_contradiction_clause,[],[f28735])).

fof(f28735,plain,
    ( $false
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | ~ spl10_289
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(subsumption_resolution,[],[f28733,f25619])).

fof(f25619,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5)),sK2)
    | ~ spl10_289 ),
    inference(avatar_component_clause,[],[f25618])).

fof(f25618,plain,
    ( spl10_289
  <=> ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_289])])).

fof(f28733,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5)),sK2)
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56
    | ~ spl10_280
    | ~ spl10_292
    | ~ spl10_310
    | ~ spl10_396 ),
    inference(backward_demodulation,[],[f28633,f25575])).

fof(f28589,plain,
    ( spl10_396
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_30
    | spl10_33 ),
    inference(avatar_split_clause,[],[f26279,f302,f295,f267,f260,f222,f208,f201,f174,f28587])).

fof(f201,plain,
    ( spl10_10
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f208,plain,
    ( spl10_12
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f222,plain,
    ( spl10_16
  <=> v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f302,plain,
    ( spl10_33
  <=> k2_struct_0(sK3) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_33])])).

fof(f26279,plain,
    ( u1_struct_0(sK2) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_24
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f26278,f261])).

fof(f26278,plain,
    ( k2_struct_0(sK2) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,u1_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_26
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f26124,f268])).

fof(f26124,plain,
    ( k2_struct_0(sK2) = k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k2_struct_0(sK3))
    | ~ spl10_4
    | ~ spl10_10
    | ~ spl10_12
    | ~ spl10_16
    | ~ spl10_30
    | ~ spl10_33 ),
    inference(unit_resulting_resolution,[],[f202,f209,f175,f303,f223,f296,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t52_tops_2)).

fof(f223,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f222])).

fof(f303,plain,
    ( k2_struct_0(sK3) != k1_xboole_0
    | ~ spl10_33 ),
    inference(avatar_component_clause,[],[f302])).

fof(f209,plain,
    ( l1_struct_0(sK3)
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f208])).

fof(f202,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f28578,plain,
    ( spl10_394
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f28173,f26097,f28576])).

fof(f26097,plain,
    ( spl10_306
  <=> k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_306])])).

fof(f28173,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))),u1_struct_0(sK3))
    | ~ spl10_306 ),
    inference(superposition,[],[f26650,f878])).

fof(f26650,plain,
    ( ! [X159] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(sK5,X159))))),u1_struct_0(sK3))
    | ~ spl10_306 ),
    inference(superposition,[],[f8935,f26098])).

fof(f26098,plain,
    ( k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5
    | ~ spl10_306 ),
    inference(avatar_component_clause,[],[f26097])).

fof(f8935,plain,(
    ! [X10,X11,X9] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X9,X10),X11))))),X9) ),
    inference(superposition,[],[f8856,f907])).

fof(f8856,plain,(
    ! [X14,X12,X15,X13] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X12,X13),X14))),X15),X12) ),
    inference(superposition,[],[f8780,f907])).

fof(f8780,plain,(
    ! [X4,X2,X0,X3,X1] : r1_tarski(k6_subset_1(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4),X0) ),
    inference(unit_resulting_resolution,[],[f2394,f138])).

fof(f2394,plain,(
    ! [X4,X2,X0,X3,X1] : m1_subset_1(k6_subset_1(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f2356,f2358])).

fof(f2358,plain,(
    ! [X4,X2,X0,X3,X1] : k6_subset_1(k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) = k7_subset_1(X0,k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4) ),
    inference(unit_resulting_resolution,[],[f1496,f155])).

fof(f2356,plain,(
    ! [X4,X2,X0,X3,X1] : m1_subset_1(k7_subset_1(X0,k6_subset_1(k6_subset_1(k6_subset_1(X0,X1),X2),X3),X4),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1496,f142])).

fof(f28571,plain,
    ( spl10_392
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26651,f26097,f28569])).

fof(f26651,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))),u1_struct_0(sK3))
    | ~ spl10_306 ),
    inference(superposition,[],[f9027,f26098])).

fof(f9027,plain,(
    ! [X6,X7] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(X6,X7))))))),X6) ),
    inference(superposition,[],[f8904,f907])).

fof(f8904,plain,(
    ! [X10,X11,X9] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(X9,X10))))),X11),X9) ),
    inference(superposition,[],[f8849,f907])).

fof(f8849,plain,(
    ! [X14,X12,X15,X13] : r1_tarski(k6_subset_1(k6_subset_1(sK7(k1_zfmisc_1(k6_subset_1(X12,X13))),X14),X15),X12) ),
    inference(superposition,[],[f8780,f907])).

fof(f28218,plain,
    ( ~ spl10_391
    | ~ spl10_218
    | spl10_235 ),
    inference(avatar_split_clause,[],[f28079,f24775,f22323,f28216])).

fof(f28216,plain,
    ( spl10_391
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_391])])).

fof(f28079,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))))
    | ~ spl10_218
    | ~ spl10_235 ),
    inference(unit_resulting_resolution,[],[f24776,f22324,f146])).

fof(f28193,plain,
    ( ~ spl10_389
    | spl10_235
    | ~ spl10_338 ),
    inference(avatar_split_clause,[],[f27621,f27280,f24775,f28191])).

fof(f28191,plain,
    ( spl10_389
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_389])])).

fof(f27621,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)))
    | ~ spl10_235
    | ~ spl10_338 ),
    inference(unit_resulting_resolution,[],[f24776,f27281,f146])).

fof(f28186,plain,
    ( spl10_386
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26698,f26097,f22415,f28184])).

fof(f26698,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f26593,f22416])).

fof(f26593,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_306 ),
    inference(superposition,[],[f3034,f26098])).

fof(f3034,plain,(
    ! [X28,X27] :
      ( r2_hidden(k3_subset_1(X27,sK7(k1_zfmisc_1(k6_subset_1(X27,X28)))),k1_zfmisc_1(X27))
      | v1_xboole_0(k1_zfmisc_1(X27)) ) ),
    inference(resolution,[],[f1822,f134])).

fof(f1822,plain,(
    ! [X0,X1] : m1_subset_1(k3_subset_1(X0,sK7(k1_zfmisc_1(k6_subset_1(X0,X1)))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f1663,f135])).

fof(f28152,plain,
    ( spl10_384
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25977,f25636,f25629,f28150])).

fof(f25977,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(sK5,sK5),k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(superposition,[],[f25943,f878])).

fof(f25943,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(sK5,sK5),X0),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(superposition,[],[f25892,f878])).

fof(f25892,plain,
    ( ! [X64,X63] : r1_tarski(k6_subset_1(k6_subset_1(sK5,X63),X64),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25735,f25630])).

fof(f25735,plain,
    ( ! [X64,X63] : r1_tarski(k6_subset_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X63),X64),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f2403,f25637])).

fof(f2403,plain,(
    ! [X19,X17,X18,X16] : r1_tarski(k6_subset_1(k6_subset_1(k3_subset_1(X16,k6_subset_1(X16,X17)),X18),X19),X16) ),
    inference(superposition,[],[f2355,f883])).

fof(f883,plain,(
    ! [X0,X1] : k3_subset_1(X0,k6_subset_1(X0,X1)) = k6_subset_1(X0,k6_subset_1(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f130,f154])).

fof(f28145,plain,
    ( spl10_382
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25974,f25636,f25629,f28143])).

fof(f25974,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(superposition,[],[f25894,f890])).

fof(f25894,plain,
    ( ! [X73] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(sK5,X73))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25745,f25630])).

fof(f25745,plain,
    ( ! [X73] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)),X73))),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f2461,f25637])).

fof(f2461,plain,(
    ! [X12,X13,X11] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(k3_subset_1(X11,k6_subset_1(X11,X12)),X13))),X11) ),
    inference(superposition,[],[f2416,f883])).

fof(f2416,plain,(
    ! [X10,X11,X9] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X9,X10),X11))),X9) ),
    inference(superposition,[],[f2355,f907])).

fof(f28126,plain,
    ( spl10_380
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25959,f25636,f25629,f28124])).

fof(f25959,plain,
    ( r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK5)),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(superposition,[],[f25893,f878])).

fof(f25893,plain,
    ( ! [X72] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK5)),X72),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25742,f25630])).

fof(f25742,plain,
    ( ! [X72] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))),X72),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f2444,f25637])).

fof(f2444,plain,(
    ! [X12,X13,X11] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k3_subset_1(X11,k6_subset_1(X11,X12)))),X13),X11) ),
    inference(superposition,[],[f2409,f883])).

fof(f2409,plain,(
    ! [X10,X11,X9] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(k6_subset_1(X9,X10))),X11),X9) ),
    inference(superposition,[],[f2355,f907])).

fof(f28119,plain,
    ( spl10_378
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25931,f25636,f25629,f479,f174,f28117])).

fof(f28117,plain,
    ( spl10_378
  <=> r1_tarski(k10_relat_1(sK4,sK7(k1_zfmisc_1(sK5))),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_378])])).

fof(f25931,plain,
    ( r1_tarski(k10_relat_1(sK4,sK7(k1_zfmisc_1(sK5))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25858,f25630])).

fof(f25858,plain,
    ( r1_tarski(k10_relat_1(sK4,sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292 ),
    inference(superposition,[],[f17594,f25637])).

fof(f17594,plain,
    ( ! [X6,X7] : r1_tarski(k10_relat_1(sK4,sK7(k1_zfmisc_1(k3_subset_1(X6,k6_subset_1(X6,X7))))),k10_relat_1(sK4,X6))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f17557,f883])).

fof(f17557,plain,
    ( ! [X6,X7] : r1_tarski(k10_relat_1(sK4,sK7(k1_zfmisc_1(k6_subset_1(X6,X7)))),k10_relat_1(sK4,X6))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f17449,f907])).

fof(f17449,plain,
    ( ! [X2,X0,X1] : r1_tarski(k10_relat_1(sK4,k6_subset_1(k6_subset_1(X0,X1),X2)),k10_relat_1(sK4,X0))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f17055,f16903])).

fof(f17055,plain,
    ( ! [X134,X136,X135] : r1_tarski(k6_subset_1(k10_relat_1(sK4,k6_subset_1(X134,X135)),X136),k10_relat_1(sK4,X134))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f1476,f16903])).

fof(f28103,plain,
    ( spl10_376
    | ~ spl10_218
    | spl10_229 ),
    inference(avatar_split_clause,[],[f28082,f22415,f22323,f28101])).

fof(f28101,plain,
    ( spl10_376
  <=> r2_hidden(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_376])])).

fof(f28082,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_218
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f22324,f134])).

fof(f28074,plain,
    ( spl10_218
    | ~ spl10_216 ),
    inference(avatar_split_clause,[],[f22318,f22314,f22323])).

fof(f22314,plain,
    ( spl10_216
  <=> r1_tarski(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_216])])).

fof(f22318,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_216 ),
    inference(resolution,[],[f22315,f139])).

fof(f22315,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),u1_struct_0(sK3))
    | ~ spl10_216 ),
    inference(avatar_component_clause,[],[f22314])).

fof(f28062,plain,
    ( ~ spl10_375
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26702,f26097,f22415,f28060])).

fof(f28060,plain,
    ( spl10_375
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_375])])).

fof(f26702,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f26662,f22416])).

fof(f26662,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_306 ),
    inference(superposition,[],[f15825,f26098])).

fof(f15825,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k1_zfmisc_1(X6),k3_subset_1(X6,sK7(k1_zfmisc_1(k6_subset_1(X6,X7)))))
      | v1_xboole_0(k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f14086,f907])).

fof(f14086,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X3),k3_subset_1(X3,k6_subset_1(k6_subset_1(X3,X4),X5)))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f1489,f132])).

fof(f1489,plain,(
    ! [X30,X28,X29] :
      ( r2_hidden(k3_subset_1(X28,k6_subset_1(k6_subset_1(X28,X29),X30)),k1_zfmisc_1(X28))
      | v1_xboole_0(k1_zfmisc_1(X28)) ) ),
    inference(backward_demodulation,[],[f1389,f1186])).

fof(f1186,plain,(
    ! [X30,X28,X29] :
      ( v1_xboole_0(k1_zfmisc_1(X28))
      | r2_hidden(k3_subset_1(X28,k7_subset_1(X28,k6_subset_1(X28,X29),X30)),k1_zfmisc_1(X28)) ) ),
    inference(resolution,[],[f774,f134])).

fof(f774,plain,(
    ! [X2,X0,X1] : m1_subset_1(k3_subset_1(X0,k7_subset_1(X0,k6_subset_1(X0,X1),X2)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f740,f135])).

fof(f27945,plain,
    ( spl10_372
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25929,f25636,f25629,f479,f174,f27943])).

fof(f27943,plain,
    ( spl10_372
  <=> r1_tarski(sK7(k1_zfmisc_1(k10_relat_1(sK4,sK5))),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_372])])).

fof(f25929,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k10_relat_1(sK4,sK5))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25851,f25630])).

fof(f25851,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292 ),
    inference(superposition,[],[f17280,f25637])).

fof(f17280,plain,
    ( ! [X208,X209] : r1_tarski(sK7(k1_zfmisc_1(k10_relat_1(sK4,k3_subset_1(X208,k6_subset_1(X208,X209))))),k10_relat_1(sK4,X208))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17078,f17259])).

fof(f17259,plain,
    ( ! [X120,X119] : k3_subset_1(k10_relat_1(sK4,X119),k10_relat_1(sK4,k6_subset_1(X119,X120))) = k10_relat_1(sK4,k3_subset_1(X119,k6_subset_1(X119,X120)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17258,f883])).

fof(f17258,plain,
    ( ! [X120,X119] : k3_subset_1(k10_relat_1(sK4,X119),k10_relat_1(sK4,k6_subset_1(X119,X120))) = k10_relat_1(sK4,k6_subset_1(X119,k6_subset_1(X119,X120)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17049,f16903])).

fof(f17049,plain,
    ( ! [X120,X119] : k3_subset_1(k10_relat_1(sK4,X119),k10_relat_1(sK4,k6_subset_1(X119,X120))) = k6_subset_1(k10_relat_1(sK4,X119),k10_relat_1(sK4,k6_subset_1(X119,X120)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f883,f16903])).

fof(f17078,plain,
    ( ! [X208,X209] : r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(k10_relat_1(sK4,X208),k10_relat_1(sK4,k6_subset_1(X208,X209))))),k10_relat_1(sK4,X208))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f1670,f16903])).

fof(f1670,plain,(
    ! [X6,X7] : r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(X6,k6_subset_1(X6,X7)))),X6) ),
    inference(superposition,[],[f1656,f883])).

fof(f27915,plain,
    ( spl10_370
    | spl10_229
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25887,f25636,f22415,f27913])).

fof(f27913,plain,
    ( spl10_370
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_370])])).

fof(f25887,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_292 ),
    inference(subsumption_resolution,[],[f25712,f22416])).

fof(f25712,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_292 ),
    inference(superposition,[],[f1838,f25637])).

fof(f1838,plain,(
    ! [X24,X23] :
      ( r2_hidden(sK7(k1_zfmisc_1(k6_subset_1(X23,X24))),k1_zfmisc_1(X23))
      | v1_xboole_0(k1_zfmisc_1(X23)) ) ),
    inference(resolution,[],[f1663,f134])).

fof(f27851,plain,
    ( spl10_368
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f27610,f26097,f22415,f27849])).

fof(f27849,plain,
    ( spl10_368
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_368])])).

fof(f27610,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(superposition,[],[f26696,f878])).

fof(f26696,plain,
    ( ! [X18] : r2_hidden(k3_subset_1(u1_struct_0(sK3),k6_subset_1(sK5,X18)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f26521,f22416])).

fof(f26521,plain,
    ( ! [X18] :
        ( r2_hidden(k3_subset_1(u1_struct_0(sK3),k6_subset_1(sK5,X18)),k1_zfmisc_1(u1_struct_0(sK3)))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl10_306 ),
    inference(superposition,[],[f1489,f26098])).

fof(f27844,plain,
    ( spl10_366
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27313,f27301,f27842])).

fof(f27842,plain,
    ( spl10_366
  <=> r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_366])])).

fof(f27301,plain,
    ( spl10_343
  <=> ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_343])])).

fof(f27313,plain,
    ( r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f129,f27302,f134])).

fof(f27302,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_343 ),
    inference(avatar_component_clause,[],[f27301])).

fof(f27837,plain,
    ( ~ spl10_365
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27310,f27301,f27835])).

fof(f27835,plain,
    ( spl10_365
  <=> ~ r2_hidden(k10_relat_1(sK4,u1_struct_0(sK3)),sK7(k10_relat_1(sK4,u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_365])])).

fof(f27310,plain,
    ( ~ r2_hidden(k10_relat_1(sK4,u1_struct_0(sK3)),sK7(k10_relat_1(sK4,u1_struct_0(sK3))))
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f27302,f363])).

fof(f27823,plain,
    ( spl10_362
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26682,f26097,f479,f174,f27821])).

fof(f27821,plain,
    ( spl10_362
  <=> r1_tarski(k10_relat_1(sK4,k3_subset_1(sK5,sK5)),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_362])])).

fof(f26682,plain,
    ( r1_tarski(k10_relat_1(sK4,k3_subset_1(sK5,sK5)),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_306 ),
    inference(superposition,[],[f17279,f26098])).

fof(f17279,plain,
    ( ! [X198,X197] : r1_tarski(k10_relat_1(sK4,k3_subset_1(k6_subset_1(X197,X198),k6_subset_1(X197,X198))),k10_relat_1(sK4,X197))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(forward_demodulation,[],[f17073,f17179])).

fof(f17073,plain,
    ( ! [X198,X197] : r1_tarski(k3_subset_1(k10_relat_1(sK4,k6_subset_1(X197,X198)),k10_relat_1(sK4,k6_subset_1(X197,X198))),k10_relat_1(sK4,X197))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f1653,f16903])).

fof(f1653,plain,(
    ! [X0,X1] : r1_tarski(k3_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X1)),X0) ),
    inference(superposition,[],[f1476,f878])).

fof(f27804,plain,
    ( ~ spl10_361
    | spl10_229
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25911,f25636,f22415,f27802])).

fof(f27802,plain,
    ( spl10_361
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_361])])).

fof(f25911,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))
    | ~ spl10_229
    | ~ spl10_292 ),
    inference(subsumption_resolution,[],[f25784,f22416])).

fof(f25784,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))))
    | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_292 ),
    inference(superposition,[],[f3585,f25637])).

fof(f3585,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(k1_zfmisc_1(X6),sK7(k1_zfmisc_1(k6_subset_1(X6,X7))))
      | v1_xboole_0(k1_zfmisc_1(X6)) ) ),
    inference(superposition,[],[f3351,f907])).

fof(f27797,plain,
    ( spl10_358
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25704,f25636,f27795])).

fof(f27795,plain,
    ( spl10_358
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_358])])).

fof(f25704,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_292 ),
    inference(superposition,[],[f1663,f25637])).

fof(f27790,plain,
    ( spl10_356
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24733,f22415,f27788])).

fof(f27788,plain,
    ( spl10_356
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_356])])).

fof(f24733,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f1660,f22416,f134])).

fof(f27706,plain,
    ( ~ spl10_355
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24574,f22415,f27704])).

fof(f27704,plain,
    ( spl10_355
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_355])])).

fof(f24574,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK3))))))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f3570])).

fof(f3570,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X3),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(X3)))))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f3340,f907])).

fof(f3340,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X2),k6_subset_1(sK7(k1_zfmisc_1(X2)),X3))
      | v1_xboole_0(k1_zfmisc_1(X2)) ) ),
    inference(resolution,[],[f1428,f132])).

fof(f1428,plain,(
    ! [X19,X18] :
      ( r2_hidden(k6_subset_1(sK7(k1_zfmisc_1(X18)),X19),k1_zfmisc_1(X18))
      | v1_xboole_0(k1_zfmisc_1(X18)) ) ),
    inference(backward_demodulation,[],[f1398,f803])).

fof(f803,plain,(
    ! [X19,X18] :
      ( v1_xboole_0(k1_zfmisc_1(X18))
      | r2_hidden(k7_subset_1(X18,sK7(k1_zfmisc_1(X18)),X19),k1_zfmisc_1(X18)) ) ),
    inference(resolution,[],[f742,f134])).

fof(f27600,plain,
    ( ~ spl10_353
    | ~ spl10_30
    | spl10_49
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27307,f27301,f415,f295,f27598])).

fof(f27598,plain,
    ( spl10_353
  <=> ~ r2_hidden(u1_struct_0(sK2),sK7(k10_relat_1(sK4,u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_353])])).

fof(f415,plain,
    ( spl10_49
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_49])])).

fof(f27307,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK7(k10_relat_1(sK4,u1_struct_0(sK3))))
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f27302,f5038])).

fof(f5038,plain,
    ( ! [X1] :
        ( ~ r2_hidden(u1_struct_0(sK2),sK7(k10_relat_1(sK4,X1)))
        | v1_xboole_0(k10_relat_1(sK4,X1)) )
    | ~ spl10_30
    | ~ spl10_49 ),
    inference(resolution,[],[f4654,f132])).

fof(f4654,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(k10_relat_1(sK4,X0)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X0)) )
    | ~ spl10_30
    | ~ spl10_49 ),
    inference(subsumption_resolution,[],[f4653,f416])).

fof(f416,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl10_49 ),
    inference(avatar_component_clause,[],[f415])).

fof(f4653,plain,
    ( ! [X0] :
        ( v1_xboole_0(k10_relat_1(sK4,X0))
        | v1_xboole_0(u1_struct_0(sK2))
        | r2_hidden(sK7(k10_relat_1(sK4,X0)),u1_struct_0(sK2)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f3835,f134])).

fof(f3835,plain,
    ( ! [X0] :
        ( m1_subset_1(sK7(k10_relat_1(sK4,X0)),u1_struct_0(sK2))
        | v1_xboole_0(k10_relat_1(sK4,X0)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f3741,f360])).

fof(f3741,plain,
    ( ! [X6,X5] :
        ( ~ r2_hidden(X5,k10_relat_1(sK4,X6))
        | m1_subset_1(X5,u1_struct_0(sK2)) )
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f3330])).

fof(f3330,plain,
    ( ! [X6,X5] :
        ( m1_subset_1(X5,u1_struct_0(sK2))
        | ~ r2_hidden(X5,k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X6)) )
    | ~ spl10_30 ),
    inference(resolution,[],[f1935,f146])).

fof(f27334,plain,
    ( ~ spl10_351
    | ~ spl10_94
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27312,f27301,f4197,f27332])).

fof(f27332,plain,
    ( spl10_351
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_351])])).

fof(f4197,plain,
    ( spl10_94
  <=> ! [X12] : r2_hidden(k10_relat_1(sK4,X12),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_94])])).

fof(f27312,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_94
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f4204,f27302,f134])).

fof(f4204,plain,
    ( ! [X0] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k10_relat_1(sK4,X0))
    | ~ spl10_94 ),
    inference(unit_resulting_resolution,[],[f4198,f132])).

fof(f4198,plain,
    ( ! [X12] : r2_hidden(k10_relat_1(sK4,X12),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_94 ),
    inference(avatar_component_clause,[],[f4197])).

fof(f27327,plain,
    ( spl10_348
    | ~ spl10_30
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27309,f27301,f295,f27325])).

fof(f27325,plain,
    ( spl10_348
  <=> m1_subset_1(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_348])])).

fof(f27309,plain,
    ( m1_subset_1(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),u1_struct_0(sK2))
    | ~ spl10_30
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f27302,f3835])).

fof(f27320,plain,
    ( spl10_346
    | ~ spl10_30
    | spl10_49
    | spl10_343 ),
    inference(avatar_split_clause,[],[f27308,f27301,f415,f295,f27318])).

fof(f27318,plain,
    ( spl10_346
  <=> r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_346])])).

fof(f27308,plain,
    ( r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK3))),u1_struct_0(sK2))
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_343 ),
    inference(unit_resulting_resolution,[],[f27302,f4654])).

fof(f27306,plain,
    ( ~ spl10_343
    | spl10_344
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25927,f25636,f25629,f479,f174,f27304,f27301])).

fof(f27304,plain,
    ( spl10_344
  <=> ! [X188] : ~ r2_hidden(X188,k10_relat_1(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_344])])).

fof(f25927,plain,
    ( ! [X188] :
        ( ~ r2_hidden(X188,k10_relat_1(sK4,sK5))
        | ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK3))) )
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25848,f25630])).

fof(f25848,plain,
    ( ! [X188] :
        ( ~ r2_hidden(X188,k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))))
        | ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK3))) )
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292 ),
    inference(superposition,[],[f17265,f25637])).

fof(f17265,plain,
    ( ! [X101,X102,X100] :
        ( ~ r2_hidden(X102,k10_relat_1(sK4,k3_subset_1(X100,k6_subset_1(X100,X101))))
        | ~ v1_xboole_0(k10_relat_1(sK4,X100)) )
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(backward_demodulation,[],[f17259,f17041])).

fof(f17041,plain,
    ( ! [X101,X102,X100] :
        ( ~ r2_hidden(X102,k3_subset_1(k10_relat_1(sK4,X100),k10_relat_1(sK4,k6_subset_1(X100,X101))))
        | ~ v1_xboole_0(k10_relat_1(sK4,X100)) )
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f536,f16903])).

fof(f536,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,k3_subset_1(X2,k6_subset_1(X2,X4)))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f514,f147])).

fof(f27289,plain,
    ( spl10_340
    | ~ spl10_264 ),
    inference(avatar_split_clause,[],[f25406,f25379,f27287])).

fof(f25406,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_264 ),
    inference(unit_resulting_resolution,[],[f25380,f135])).

fof(f27282,plain,
    ( spl10_338
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f25382,f25372,f27280])).

fof(f25382,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f25373,f135])).

fof(f27275,plain,
    ( ~ spl10_337
    | spl10_213 ),
    inference(avatar_split_clause,[],[f25104,f22228,f27273])).

fof(f27273,plain,
    ( spl10_337
  <=> ~ r2_hidden(sK6(sK2,sK4,sK3),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_337])])).

fof(f22228,plain,
    ( spl10_213
  <=> ~ m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_213])])).

fof(f25104,plain,
    ( ~ r2_hidden(sK6(sK2,sK4,sK3),sK7(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))))
    | ~ spl10_213 ),
    inference(unit_resulting_resolution,[],[f22229,f583])).

fof(f22229,plain,
    ( ~ m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_213 ),
    inference(avatar_component_clause,[],[f22228])).

fof(f27124,plain,
    ( spl10_334
    | ~ spl10_302 ),
    inference(avatar_split_clause,[],[f26000,f25995,f27122])).

fof(f25995,plain,
    ( spl10_302
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_302])])).

fof(f26000,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_302 ),
    inference(unit_resulting_resolution,[],[f25996,f139])).

fof(f25996,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),u1_struct_0(sK3))
    | ~ spl10_302 ),
    inference(avatar_component_clause,[],[f25995])).

fof(f27117,plain,
    ( spl10_332
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25906,f25636,f25629,f27115])).

fof(f25906,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25775,f25630])).

fof(f25775,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_292 ),
    inference(superposition,[],[f3293,f25637])).

fof(f3293,plain,(
    ! [X6,X7] : m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(X6,k6_subset_1(X6,X7)))))),k1_zfmisc_1(X6)) ),
    inference(superposition,[],[f2491,f883])).

fof(f2491,plain,(
    ! [X0,X1] : m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(X0,X1))))),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f2450,f139])).

fof(f2450,plain,(
    ! [X6,X7] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k6_subset_1(X6,X7))))),X6) ),
    inference(superposition,[],[f2409,f907])).

fof(f27110,plain,
    ( ~ spl10_331
    | spl10_235
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25484,f25199,f24775,f27108])).

fof(f27108,plain,
    ( spl10_331
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_331])])).

fof(f25199,plain,
    ( spl10_240
  <=> m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_240])])).

fof(f25484,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))))
    | ~ spl10_235
    | ~ spl10_240 ),
    inference(superposition,[],[f25276,f890])).

fof(f25276,plain,
    ( ! [X0] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k6_subset_1(sK5,X0))
    | ~ spl10_235
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f24776,f25223,f146])).

fof(f25223,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(sK5,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(forward_demodulation,[],[f25206,f25209])).

fof(f25209,plain,
    ( ! [X0] : k6_subset_1(sK5,X0) = k7_subset_1(u1_struct_0(sK3),sK5,X0)
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f155])).

fof(f25200,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(avatar_component_clause,[],[f25199])).

fof(f25206,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(u1_struct_0(sK3),sK5,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f142])).

fof(f27093,plain,
    ( ~ spl10_329
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26989,f26097,f22415,f27091])).

fof(f27091,plain,
    ( spl10_329
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_329])])).

fof(f26989,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(superposition,[],[f26701,f907])).

fof(f26701,plain,
    ( ! [X175] : ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k6_subset_1(sK5,X175))))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f26661,f22416])).

fof(f26661,plain,
    ( ! [X175] :
        ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k6_subset_1(sK5,X175))))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl10_306 ),
    inference(superposition,[],[f15383,f26098])).

fof(f15383,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(k1_zfmisc_1(X3),sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X3,X4),X5))))
      | v1_xboole_0(k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f2784,f132])).

fof(f2784,plain,(
    ! [X39,X37,X38] :
      ( r2_hidden(sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X37,X38),X39))),k1_zfmisc_1(X37))
      | v1_xboole_0(k1_zfmisc_1(X37)) ) ),
    inference(resolution,[],[f2390,f134])).

fof(f2390,plain,(
    ! [X10,X11,X9] : m1_subset_1(sK7(k1_zfmisc_1(k6_subset_1(k6_subset_1(X9,X10),X11))),k1_zfmisc_1(X9)) ),
    inference(superposition,[],[f1496,f907])).

fof(f27086,plain,
    ( ~ spl10_327
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26986,f26097,f22415,f27084])).

fof(f27084,plain,
    ( spl10_327
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_327])])).

fof(f26986,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(superposition,[],[f26701,f878])).

fof(f27013,plain,
    ( spl10_324
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26922,f26097,f22415,f27011])).

fof(f26922,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(superposition,[],[f26697,f907])).

fof(f26697,plain,
    ( ! [X80] : r2_hidden(sK7(k1_zfmisc_1(k6_subset_1(sK5,X80))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(subsumption_resolution,[],[f26587,f22416])).

fof(f26587,plain,
    ( ! [X80] :
        ( r2_hidden(sK7(k1_zfmisc_1(k6_subset_1(sK5,X80))),k1_zfmisc_1(u1_struct_0(sK3)))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) )
    | ~ spl10_306 ),
    inference(superposition,[],[f2784,f26098])).

fof(f27006,plain,
    ( spl10_322
    | spl10_229
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26919,f26097,f22415,f27004])).

fof(f27004,plain,
    ( spl10_322
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_322])])).

fof(f26919,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_306 ),
    inference(superposition,[],[f26697,f878])).

fof(f26985,plain,
    ( spl10_320
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25890,f25636,f25629,f26983])).

fof(f25890,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25723,f25630])).

fof(f25723,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))))),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f2049,f25637])).

fof(f2049,plain,(
    ! [X6,X7] : r1_tarski(k3_subset_1(X6,sK7(k1_zfmisc_1(k3_subset_1(X6,k6_subset_1(X6,X7))))),X6) ),
    inference(superposition,[],[f1923,f883])).

fof(f1923,plain,(
    ! [X6,X7] : r1_tarski(k3_subset_1(X6,sK7(k1_zfmisc_1(k6_subset_1(X6,X7)))),X6) ),
    inference(superposition,[],[f1485,f907])).

fof(f1485,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_subset_1(X0,k6_subset_1(k6_subset_1(X0,X1),X2)),X0) ),
    inference(backward_demodulation,[],[f1389,f1174])).

fof(f1174,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_subset_1(X0,k7_subset_1(X0,k6_subset_1(X0,X1),X2)),X0) ),
    inference(unit_resulting_resolution,[],[f774,f138])).

fof(f26978,plain,
    ( spl10_318
    | spl10_229
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25445,f25199,f22415,f26976])).

fof(f26976,plain,
    ( spl10_318
  <=> r2_hidden(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_318])])).

fof(f25445,plain,
    ( r2_hidden(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_240 ),
    inference(superposition,[],[f25279,f890])).

fof(f25279,plain,
    ( ! [X0] : r2_hidden(k6_subset_1(sK5,X0),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f22416,f25223,f134])).

fof(f26909,plain,
    ( spl10_316
    | ~ spl10_306 ),
    inference(avatar_split_clause,[],[f26550,f26097,f26907])).

fof(f26907,plain,
    ( spl10_316
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_316])])).

fof(f26550,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),k3_subset_1(sK5,sK5)),u1_struct_0(sK3))
    | ~ spl10_306 ),
    inference(superposition,[],[f1920,f26098])).

fof(f1920,plain,(
    ! [X0,X1] : r1_tarski(k3_subset_1(X0,k3_subset_1(k6_subset_1(X0,X1),k6_subset_1(X0,X1))),X0) ),
    inference(superposition,[],[f1485,f878])).

fof(f26839,plain,
    ( spl10_314
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24610,f22415,f26837])).

fof(f26837,plain,
    ( spl10_314
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_314])])).

fof(f24610,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f513,f22416,f134])).

fof(f26832,plain,
    ( ~ spl10_313
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24543,f22415,f26830])).

fof(f26830,plain,
    ( spl10_313
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_313])])).

fof(f24543,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f571])).

fof(f571,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(X1),k3_subset_1(X1,X1))
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f528,f132])).

fof(f528,plain,(
    ! [X6] :
      ( r2_hidden(k3_subset_1(X6,X6),k1_zfmisc_1(X6))
      | v1_xboole_0(k1_zfmisc_1(X6)) ) ),
    inference(resolution,[],[f513,f134])).

fof(f26798,plain,
    ( spl10_310
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25925,f25636,f25629,f479,f174,f26796])).

fof(f25925,plain,
    ( m1_subset_1(k10_relat_1(sK4,sK5),k1_zfmisc_1(k10_relat_1(sK4,u1_struct_0(sK3))))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25846,f25630])).

fof(f25846,plain,
    ( m1_subset_1(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))),k1_zfmisc_1(k10_relat_1(sK4,u1_struct_0(sK3))))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292 ),
    inference(superposition,[],[f17263,f25637])).

fof(f17263,plain,
    ( ! [X97,X96] : m1_subset_1(k10_relat_1(sK4,k3_subset_1(X96,k6_subset_1(X96,X97))),k1_zfmisc_1(k10_relat_1(sK4,X96)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(backward_demodulation,[],[f17259,f17039])).

fof(f17039,plain,
    ( ! [X97,X96] : m1_subset_1(k3_subset_1(k10_relat_1(sK4,X96),k10_relat_1(sK4,k6_subset_1(X96,X97))),k1_zfmisc_1(k10_relat_1(sK4,X96)))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f514,f16903])).

fof(f26791,plain,
    ( spl10_308
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25701,f25636,f26789])).

fof(f26789,plain,
    ( spl10_308
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_308])])).

fof(f25701,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),sK5))),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f1656,f25637])).

fof(f26099,plain,
    ( spl10_306
    | ~ spl10_240
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25528,f25503,f25199,f26097])).

fof(f25528,plain,
    ( k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5
    | ~ spl10_240
    | ~ spl10_274 ),
    inference(forward_demodulation,[],[f25513,f25204])).

fof(f25204,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = sK5
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f136])).

fof(f25513,plain,
    ( k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)) = k6_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25504,f154])).

fof(f26054,plain,
    ( spl10_304
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25298,f25199,f26052])).

fof(f25298,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(superposition,[],[f25223,f890])).

fof(f25997,plain,
    ( spl10_302
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25968,f25636,f25629,f25995])).

fof(f25968,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK5,sK5))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(superposition,[],[f25894,f878])).

fof(f25990,plain,
    ( spl10_300
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25895,f25636,f25629,f25988])).

fof(f25895,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK5)))),u1_struct_0(sK3))
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25750,f25630])).

fof(f25750,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5)))))),u1_struct_0(sK3))
    | ~ spl10_292 ),
    inference(superposition,[],[f2498,f25637])).

fof(f2498,plain,(
    ! [X6,X7] : r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(k3_subset_1(X6,k6_subset_1(X6,X7)))))),X6) ),
    inference(superposition,[],[f2450,f883])).

fof(f25938,plain,
    ( spl10_298
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(avatar_split_clause,[],[f25926,f25636,f25629,f479,f174,f25936])).

fof(f25936,plain,
    ( spl10_298
  <=> r1_tarski(k10_relat_1(sK4,sK5),k10_relat_1(sK4,u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_298])])).

fof(f25926,plain,
    ( r1_tarski(k10_relat_1(sK4,sK5),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_290
    | ~ spl10_292 ),
    inference(forward_demodulation,[],[f25847,f25630])).

fof(f25847,plain,
    ( r1_tarski(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),k3_subset_1(u1_struct_0(sK3),sK5))),k10_relat_1(sK4,u1_struct_0(sK3)))
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_292 ),
    inference(superposition,[],[f17264,f25637])).

fof(f17264,plain,
    ( ! [X99,X98] : r1_tarski(k10_relat_1(sK4,k3_subset_1(X98,k6_subset_1(X98,X99))),k10_relat_1(sK4,X98))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(backward_demodulation,[],[f17259,f17040])).

fof(f17040,plain,
    ( ! [X99,X98] : r1_tarski(k3_subset_1(k10_relat_1(sK4,X98),k10_relat_1(sK4,k6_subset_1(X98,X99))),k10_relat_1(sK4,X98))
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f533,f16903])).

fof(f533,plain,(
    ! [X0,X1] : r1_tarski(k3_subset_1(X0,k6_subset_1(X0,X1)),X0) ),
    inference(unit_resulting_resolution,[],[f514,f138])).

fof(f25653,plain,
    ( ~ spl10_295
    | ~ spl10_2
    | ~ spl10_240
    | spl10_297 ),
    inference(avatar_split_clause,[],[f25652,f25649,f25199,f167,f25640])).

fof(f25649,plain,
    ( spl10_297
  <=> ~ v4_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_297])])).

fof(f25652,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ spl10_2
    | ~ spl10_240
    | ~ spl10_297 ),
    inference(unit_resulting_resolution,[],[f168,f25200,f25650,f128])).

fof(f25650,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | ~ spl10_297 ),
    inference(avatar_component_clause,[],[f25649])).

fof(f25651,plain,
    ( spl10_294
    | ~ spl10_297
    | ~ spl10_2
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25224,f25199,f167,f25649,f25643])).

fof(f25643,plain,
    ( spl10_294
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_294])])).

fof(f25224,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ spl10_2
    | ~ spl10_240 ),
    inference(subsumption_resolution,[],[f25212,f168])).

fof(f25212,plain,
    ( ~ v4_pre_topc(sK5,sK3)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ spl10_240 ),
    inference(resolution,[],[f25200,f127])).

fof(f25638,plain,
    ( spl10_292
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25208,f25199,f25636])).

fof(f25208,plain,
    ( k3_subset_1(u1_struct_0(sK3),sK5) = k6_subset_1(u1_struct_0(sK3),sK5)
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f154])).

fof(f25631,plain,
    ( spl10_290
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25204,f25199,f25629])).

fof(f25620,plain,
    ( ~ spl10_289
    | ~ spl10_0
    | ~ spl10_30
    | spl10_287 ),
    inference(avatar_split_clause,[],[f25613,f25609,f295,f160,f25618])).

fof(f25613,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK5)),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_287 ),
    inference(unit_resulting_resolution,[],[f161,f3735,f25610,f126])).

fof(f25611,plain,
    ( ~ spl10_19
    | ~ spl10_287
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f24531,f295,f25609,f231])).

fof(f24531,plain,
    ( ~ v3_pre_topc(k10_relat_1(sK4,sK5),sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3)
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f109,f3662])).

fof(f109,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,sK5),sK2)
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f25604,plain,
    ( ~ spl10_285
    | spl10_235
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25512,f25503,f24775,f25602])).

fof(f25512,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(u1_struct_0(sK3),sK5))
    | ~ spl10_235
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f24776,f25504,f146])).

fof(f25588,plain,
    ( spl10_282
    | spl10_229
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25515,f25503,f22415,f25586])).

fof(f25586,plain,
    ( spl10_282
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_282])])).

fof(f25515,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f22416,f25504,f134])).

fof(f25576,plain,
    ( spl10_280
    | ~ spl10_30
    | ~ spl10_148
    | ~ spl10_248
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25532,f25503,f25262,f6702,f295,f25574])).

fof(f6702,plain,
    ( spl10_148
  <=> sP0(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_148])])).

fof(f25262,plain,
    ( spl10_248
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_248])])).

fof(f25532,plain,
    ( v4_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK5)),sK2)
    | ~ spl10_30
    | ~ spl10_148
    | ~ spl10_248
    | ~ spl10_274 ),
    inference(forward_demodulation,[],[f25506,f3662])).

fof(f25506,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,k3_subset_1(u1_struct_0(sK3),sK5)),sK2)
    | ~ spl10_148
    | ~ spl10_248
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f6703,f25263,f25504,f120])).

fof(f120,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v4_pre_topc(X4,X2)
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)
          & v4_pre_topc(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v4_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f88,f89])).

fof(f89,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
          & v4_pre_topc(X3,X2)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)
        & v4_pre_topc(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X3),X0)
            & v4_pre_topc(X3,X2)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) )
      & ( ! [X4] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,X4),X0)
            | ~ v4_pre_topc(X4,X2)
            | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X2))) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X2,X1)
        | ? [X3] :
            ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            & v4_pre_topc(X3,X1)
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      & ( ! [X3] :
            ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
            | ~ v4_pre_topc(X3,X1)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
        | ~ sP0(X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X2,X1] :
      ( sP0(X0,X2,X1)
    <=> ! [X3] :
          ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          | ~ v4_pre_topc(X3,X1)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f25263,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ spl10_248 ),
    inference(avatar_component_clause,[],[f25262])).

fof(f6703,plain,
    ( sP0(sK2,sK4,sK3)
    | ~ spl10_148 ),
    inference(avatar_component_clause,[],[f6702])).

fof(f25569,plain,
    ( spl10_278
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25311,f25199,f25567])).

fof(f25567,plain,
    ( spl10_278
  <=> r1_tarski(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_278])])).

fof(f25311,plain,
    ( r1_tarski(k3_subset_1(sK5,sK7(k1_zfmisc_1(sK5))),u1_struct_0(sK3))
    | ~ spl10_240 ),
    inference(superposition,[],[f25274,f890])).

fof(f25274,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK5,X0),u1_struct_0(sK3))
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25223,f138])).

fof(f25548,plain,
    ( spl10_276
    | ~ spl10_274 ),
    inference(avatar_split_clause,[],[f25510,f25503,f25546])).

fof(f25546,plain,
    ( spl10_276
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_276])])).

fof(f25510,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK5),u1_struct_0(sK3))
    | ~ spl10_274 ),
    inference(unit_resulting_resolution,[],[f25504,f138])).

fof(f25505,plain,
    ( spl10_274
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25203,f25199,f25503])).

fof(f25203,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f135])).

fof(f25498,plain,
    ( ~ spl10_273
    | spl10_235
    | ~ spl10_264 ),
    inference(avatar_split_clause,[],[f25410,f25379,f24775,f25496])).

fof(f25410,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(sK5)))
    | ~ spl10_235
    | ~ spl10_264 ),
    inference(unit_resulting_resolution,[],[f24776,f25380,f146])).

fof(f25491,plain,
    ( ~ spl10_271
    | spl10_235
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f25386,f25372,f24775,f25489])).

fof(f25386,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),k3_subset_1(sK5,sK5))
    | ~ spl10_235
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f24776,f25373,f146])).

fof(f25459,plain,
    ( spl10_268
    | spl10_229
    | ~ spl10_264 ),
    inference(avatar_split_clause,[],[f25413,f25379,f22415,f25457])).

fof(f25413,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_264 ),
    inference(unit_resulting_resolution,[],[f22416,f25380,f134])).

fof(f25452,plain,
    ( spl10_266
    | spl10_229
    | ~ spl10_262 ),
    inference(avatar_split_clause,[],[f25389,f25372,f22415,f25450])).

fof(f25450,plain,
    ( spl10_266
  <=> r2_hidden(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_266])])).

fof(f25389,plain,
    ( r2_hidden(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_262 ),
    inference(unit_resulting_resolution,[],[f22416,f25373,f134])).

fof(f25381,plain,
    ( spl10_264
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25295,f25199,f25379])).

fof(f25295,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK5)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(superposition,[],[f25223,f907])).

fof(f25374,plain,
    ( spl10_262
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25292,f25199,f25372])).

fof(f25292,plain,
    ( m1_subset_1(k3_subset_1(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_240 ),
    inference(superposition,[],[f25223,f878])).

fof(f25367,plain,
    ( ~ spl10_261
    | ~ spl10_258 ),
    inference(avatar_split_clause,[],[f25356,f25349,f25365])).

fof(f25365,plain,
    ( spl10_261
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_261])])).

fof(f25349,plain,
    ( spl10_258
  <=> r2_hidden(sK7(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_258])])).

fof(f25356,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(sK5))
    | ~ spl10_258 ),
    inference(unit_resulting_resolution,[],[f25350,f132])).

fof(f25350,plain,
    ( r2_hidden(sK7(sK5),u1_struct_0(sK3))
    | ~ spl10_258 ),
    inference(avatar_component_clause,[],[f25349])).

fof(f25351,plain,
    ( spl10_258
    | spl10_37
    | ~ spl10_256 ),
    inference(avatar_split_clause,[],[f25343,f25340,f318,f25349])).

fof(f25340,plain,
    ( spl10_256
  <=> m1_subset_1(sK7(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_256])])).

fof(f25343,plain,
    ( r2_hidden(sK7(sK5),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_256 ),
    inference(unit_resulting_resolution,[],[f319,f25341,f134])).

fof(f25341,plain,
    ( m1_subset_1(sK7(sK5),u1_struct_0(sK3))
    | ~ spl10_256 ),
    inference(avatar_component_clause,[],[f25340])).

fof(f25342,plain,
    ( spl10_254
    | spl10_256
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25268,f25199,f25340,f25334])).

fof(f25334,plain,
    ( spl10_254
  <=> v1_xboole_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_254])])).

fof(f25268,plain,
    ( m1_subset_1(sK7(sK5),u1_struct_0(sK3))
    | v1_xboole_0(sK5)
    | ~ spl10_240 ),
    inference(resolution,[],[f25218,f360])).

fof(f25218,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK5)
        | m1_subset_1(X3,u1_struct_0(sK3)) )
    | ~ spl10_240 ),
    inference(resolution,[],[f25200,f146])).

fof(f25325,plain,
    ( spl10_252
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25308,f25199,f25323])).

fof(f25308,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK5)),u1_struct_0(sK3))
    | ~ spl10_240 ),
    inference(superposition,[],[f25274,f907])).

fof(f25318,plain,
    ( spl10_250
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25305,f25199,f25316])).

fof(f25305,plain,
    ( r1_tarski(k3_subset_1(sK5,sK5),u1_struct_0(sK3))
    | ~ spl10_240 ),
    inference(superposition,[],[f25274,f878])).

fof(f25264,plain,
    ( spl10_248
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25202,f25199,f237,f167,f25262])).

fof(f237,plain,
    ( spl10_20
  <=> v3_pre_topc(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f25202,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK3),sK5),sK3)
    | ~ spl10_2
    | ~ spl10_20
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f168,f238,f25200,f125])).

fof(f238,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f237])).

fof(f25257,plain,
    ( ~ spl10_247
    | spl10_235
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25207,f25199,f24775,f25255])).

fof(f25207,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK5)
    | ~ spl10_235
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f24776,f25200,f146])).

fof(f25241,plain,
    ( spl10_244
    | spl10_229
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25210,f25199,f22415,f25239])).

fof(f25210,plain,
    ( r2_hidden(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f22416,f25200,f134])).

fof(f25232,plain,
    ( spl10_242
    | ~ spl10_240 ),
    inference(avatar_split_clause,[],[f25205,f25199,f25230])).

fof(f25205,plain,
    ( r1_tarski(sK5,u1_struct_0(sK3))
    | ~ spl10_240 ),
    inference(unit_resulting_resolution,[],[f25200,f138])).

fof(f25201,plain,
    ( ~ spl10_19
    | spl10_240 ),
    inference(avatar_split_clause,[],[f107,f25199,f231])).

fof(f107,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f25185,plain,
    ( spl10_238
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24746,f22415,f25183])).

fof(f25183,plain,
    ( spl10_238
  <=> r2_hidden(sK7(k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_238])])).

fof(f24746,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(u1_struct_0(sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f129,f22416,f134])).

fof(f25162,plain,
    ( ~ spl10_237
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24607,f22415,f25160])).

fof(f25160,plain,
    ( spl10_237
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_237])])).

fof(f24607,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),sK7(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f363])).

fof(f25147,plain,
    ( ~ spl10_227
    | spl10_213 ),
    inference(avatar_split_clause,[],[f24962,f22228,f22409])).

fof(f22409,plain,
    ( spl10_227
  <=> ~ r2_hidden(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_227])])).

fof(f24962,plain,
    ( ~ r2_hidden(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_213 ),
    inference(unit_resulting_resolution,[],[f225,f22229,f146])).

fof(f25143,plain,
    ( ~ spl10_211
    | spl10_213 ),
    inference(avatar_split_clause,[],[f24960,f22228,f22219])).

fof(f22219,plain,
    ( spl10_211
  <=> ~ r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_211])])).

fof(f24960,plain,
    ( ~ r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3))
    | ~ spl10_213 ),
    inference(unit_resulting_resolution,[],[f22229,f139])).

fof(f24777,plain,
    ( ~ spl10_235
    | spl10_37
    | spl10_231 ),
    inference(avatar_split_clause,[],[f24761,f24751,f318,f24775])).

fof(f24751,plain,
    ( spl10_231
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_231])])).

fof(f24761,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_37
    | ~ spl10_231 ),
    inference(unit_resulting_resolution,[],[f319,f24752,f134])).

fof(f24752,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_231 ),
    inference(avatar_component_clause,[],[f24751])).

fof(f24760,plain,
    ( spl10_232
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24609,f22415,f24758])).

fof(f24758,plain,
    ( spl10_232
  <=> r2_hidden(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_232])])).

fof(f24609,plain,
    ( r2_hidden(u1_struct_0(sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f225,f22416,f134])).

fof(f24753,plain,
    ( ~ spl10_231
    | spl10_229 ),
    inference(avatar_split_clause,[],[f24538,f22415,f24751])).

fof(f24538,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_229 ),
    inference(unit_resulting_resolution,[],[f22416,f462])).

fof(f462,plain,(
    ! [X1] :
      ( ~ r2_hidden(k1_zfmisc_1(X1),X1)
      | v1_xboole_0(k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f357,f132])).

fof(f357,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f134,f225])).

fof(f24533,plain,
    ( ~ spl10_210
    | spl10_213 ),
    inference(avatar_contradiction_clause,[],[f24532])).

fof(f24532,plain,
    ( $false
    | ~ spl10_210
    | ~ spl10_213 ),
    inference(subsumption_resolution,[],[f22229,f22226])).

fof(f22226,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_210 ),
    inference(resolution,[],[f22223,f139])).

fof(f22223,plain,
    ( r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3))
    | ~ spl10_210 ),
    inference(avatar_component_clause,[],[f22222])).

fof(f24529,plain,
    ( spl10_44
    | ~ spl10_228 ),
    inference(avatar_split_clause,[],[f23057,f22418,f393])).

fof(f22418,plain,
    ( spl10_228
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_228])])).

fof(f23057,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_228 ),
    inference(backward_demodulation,[],[f22421,f22419])).

fof(f22419,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_228 ),
    inference(avatar_component_clause,[],[f22418])).

fof(f22421,plain,
    ( k1_zfmisc_1(u1_struct_0(sK3)) = k1_xboole_0
    | ~ spl10_228 ),
    inference(unit_resulting_resolution,[],[f22419,f112])).

fof(f22420,plain,
    ( spl10_226
    | spl10_228
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22253,f22231,f22418,f22412])).

fof(f22253,plain,
    ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK3)))
    | r2_hidden(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(resolution,[],[f22232,f134])).

fof(f22404,plain,
    ( spl10_224
    | spl10_19
    | ~ spl10_30
    | ~ spl10_214
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f22356,f22353,f22262,f295,f231,f22402])).

fof(f22356,plain,
    ( v3_pre_topc(k10_relat_1(sK4,k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3))),sK2)
    | ~ spl10_19
    | ~ spl10_30
    | ~ spl10_214
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f22263,f22354,f3734])).

fof(f22395,plain,
    ( spl10_222
    | ~ spl10_220 ),
    inference(avatar_split_clause,[],[f22360,f22353,f22393])).

fof(f22393,plain,
    ( spl10_222
  <=> r1_tarski(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_222])])).

fof(f22360,plain,
    ( r1_tarski(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),u1_struct_0(sK3))
    | ~ spl10_220 ),
    inference(unit_resulting_resolution,[],[f22354,f138])).

fof(f22355,plain,
    ( spl10_220
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22235,f22231,f22353])).

fof(f22235,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f22232,f135])).

fof(f22325,plain,
    ( spl10_218
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22293,f22231,f22323])).

fof(f22293,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_212 ),
    inference(superposition,[],[f22254,f907])).

fof(f22316,plain,
    ( spl10_216
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22306,f22231,f22314])).

fof(f22306,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK6(sK2,sK4,sK3))),u1_struct_0(sK3))
    | ~ spl10_212 ),
    inference(superposition,[],[f22273,f907])).

fof(f22264,plain,
    ( spl10_214
    | ~ spl10_2
    | ~ spl10_208
    | ~ spl10_212 ),
    inference(avatar_split_clause,[],[f22234,f22231,f22215,f167,f22262])).

fof(f22234,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK3),sK6(sK2,sK4,sK3)),sK3)
    | ~ spl10_2
    | ~ spl10_208
    | ~ spl10_212 ),
    inference(unit_resulting_resolution,[],[f168,f22216,f22232,f127])).

fof(f22233,plain,
    ( spl10_212
    | spl10_149 ),
    inference(avatar_split_clause,[],[f22206,f6699,f22231])).

fof(f22206,plain,
    ( m1_subset_1(sK6(sK2,sK4,sK3),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl10_149 ),
    inference(unit_resulting_resolution,[],[f6700,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f22224,plain,
    ( spl10_210
    | spl10_149 ),
    inference(avatar_split_clause,[],[f22209,f6699,f22222])).

fof(f22209,plain,
    ( r1_tarski(sK6(sK2,sK4,sK3),u1_struct_0(sK3))
    | ~ spl10_149 ),
    inference(unit_resulting_resolution,[],[f6700,f1374])).

fof(f1374,plain,(
    ! [X6,X8,X7] :
      ( r1_tarski(sK6(X6,X7,X8),u1_struct_0(X8))
      | sP0(X6,X7,X8) ) ),
    inference(resolution,[],[f121,f138])).

fof(f22217,plain,
    ( spl10_208
    | spl10_149 ),
    inference(avatar_split_clause,[],[f22207,f6699,f22215])).

fof(f22207,plain,
    ( v4_pre_topc(sK6(sK2,sK4,sK3),sK3)
    | ~ spl10_149 ),
    inference(unit_resulting_resolution,[],[f6700,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v4_pre_topc(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f22204,plain,
    ( ~ spl10_149
    | spl10_19
    | ~ spl10_206 ),
    inference(avatar_split_clause,[],[f22201,f22198,f231,f6699])).

fof(f22201,plain,
    ( ~ sP0(sK2,sK4,sK3)
    | ~ spl10_19
    | ~ spl10_206 ),
    inference(unit_resulting_resolution,[],[f232,f22199,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | v5_pre_topc(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f22200,plain,
    ( spl10_206
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f22018,f295,f222,f174,f167,f160,f22198])).

fof(f22018,plain,
    ( sP1(sK3,sK4,sK2)
    | ~ spl10_0
    | ~ spl10_2
    | ~ spl10_4
    | ~ spl10_16
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f161,f168,f175,f223,f296,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | sP1(X1,X2,X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X1,X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(definition_folding,[],[f52,f75,f74])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',d12_pre_topc)).

fof(f20693,plain,
    ( ~ spl10_205
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4349,f4305,f20691])).

fof(f20691,plain,
    ( spl10_205
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_205])])).

fof(f4305,plain,
    ( spl10_101
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_101])])).

fof(f4349,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f1845,f4306,f146])).

fof(f4306,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_101 ),
    inference(avatar_component_clause,[],[f4305])).

fof(f1845,plain,(
    ! [X8] : m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(X8,sK7(k1_zfmisc_1(X8))))),k1_zfmisc_1(X8)) ),
    inference(superposition,[],[f1663,f890])).

fof(f20632,plain,
    ( ~ spl10_203
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4324,f4305,f20630])).

fof(f20630,plain,
    ( spl10_203
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))),sK7(k1_zfmisc_1(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_203])])).

fof(f4324,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))),sK7(k1_zfmisc_1(u1_struct_0(sK2)))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f1704,f4306,f146])).

fof(f1704,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(sK7(k1_zfmisc_1(X0)),sK7(k1_zfmisc_1(X0))),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f1421,f878])).

fof(f1421,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(sK7(k1_zfmisc_1(X0)),X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f1398,f742])).

fof(f20615,plain,
    ( ~ spl10_201
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4320,f4305,f20613])).

fof(f20613,plain,
    ( spl10_201
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_201])])).

fof(f4320,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2)))))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f1802,f4306,f146])).

fof(f20576,plain,
    ( spl10_198
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4266,f4191,f20574])).

fof(f20574,plain,
    ( spl10_198
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_198])])).

fof(f4191,plain,
    ( spl10_93
  <=> ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_93])])).

fof(f4266,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f1845,f4192,f134])).

fof(f4192,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(avatar_component_clause,[],[f4191])).

fof(f20547,plain,
    ( spl10_196
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4237,f4191,f20545])).

fof(f20545,plain,
    ( spl10_196
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2)))))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_196])])).

fof(f4237,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2)))))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f1802,f4192,f134])).

fof(f19155,plain,
    ( spl10_194
    | ~ spl10_192 ),
    inference(avatar_split_clause,[],[f18934,f18930,f19153])).

fof(f19153,plain,
    ( spl10_194
  <=> k3_subset_1(k10_relat_1(sK4,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_194])])).

fof(f18930,plain,
    ( spl10_192
  <=> k6_subset_1(k10_relat_1(sK4,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_192])])).

fof(f18934,plain,
    ( k3_subset_1(k10_relat_1(sK4,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_192 ),
    inference(superposition,[],[f18931,f878])).

fof(f18931,plain,
    ( k6_subset_1(k10_relat_1(sK4,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_192 ),
    inference(avatar_component_clause,[],[f18930])).

fof(f18932,plain,
    ( spl10_192
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_70 ),
    inference(avatar_split_clause,[],[f18701,f949,f479,f174,f18930])).

fof(f18701,plain,
    ( k6_subset_1(k10_relat_1(sK4,k1_xboole_0),k10_relat_1(sK4,k1_xboole_0)) = k10_relat_1(sK4,k1_xboole_0)
    | ~ spl10_4
    | ~ spl10_56
    | ~ spl10_70 ),
    inference(superposition,[],[f18460,f950])).

fof(f18043,plain,
    ( spl10_190
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17755,f17743,f18041])).

fof(f18041,plain,
    ( spl10_190
  <=> r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),k10_relat_1(sK4,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_190])])).

fof(f17743,plain,
    ( spl10_177
  <=> ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_177])])).

fof(f17755,plain,
    ( r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),k10_relat_1(sK4,u1_struct_0(sK2)))
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f129,f17744,f134])).

fof(f17744,plain,
    ( ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK2)))
    | ~ spl10_177 ),
    inference(avatar_component_clause,[],[f17743])).

fof(f18036,plain,
    ( ~ spl10_189
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17752,f17743,f18034])).

fof(f18034,plain,
    ( spl10_189
  <=> ~ r2_hidden(k10_relat_1(sK4,u1_struct_0(sK2)),sK7(k10_relat_1(sK4,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_189])])).

fof(f17752,plain,
    ( ~ r2_hidden(k10_relat_1(sK4,u1_struct_0(sK2)),sK7(k10_relat_1(sK4,u1_struct_0(sK2))))
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f17744,f363])).

fof(f18029,plain,
    ( ~ spl10_187
    | ~ spl10_30
    | spl10_49
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17749,f17743,f415,f295,f18027])).

fof(f18027,plain,
    ( spl10_187
  <=> ~ r2_hidden(u1_struct_0(sK2),sK7(k10_relat_1(sK4,u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_187])])).

fof(f17749,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK7(k10_relat_1(sK4,u1_struct_0(sK2))))
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f17744,f5038])).

fof(f17776,plain,
    ( ~ spl10_185
    | ~ spl10_94
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17754,f17743,f4197,f17774])).

fof(f17774,plain,
    ( spl10_185
  <=> ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k10_relat_1(sK4,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_185])])).

fof(f17754,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),k10_relat_1(sK4,u1_struct_0(sK2)))
    | ~ spl10_94
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f4204,f17744,f134])).

fof(f17769,plain,
    ( spl10_182
    | ~ spl10_30
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17751,f17743,f295,f17767])).

fof(f17767,plain,
    ( spl10_182
  <=> m1_subset_1(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_182])])).

fof(f17751,plain,
    ( m1_subset_1(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl10_30
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f17744,f3835])).

fof(f17762,plain,
    ( spl10_180
    | ~ spl10_30
    | spl10_49
    | spl10_177 ),
    inference(avatar_split_clause,[],[f17750,f17743,f415,f295,f17760])).

fof(f17760,plain,
    ( spl10_180
  <=> r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_180])])).

fof(f17750,plain,
    ( r2_hidden(sK7(k10_relat_1(sK4,u1_struct_0(sK2))),u1_struct_0(sK2))
    | ~ spl10_30
    | ~ spl10_49
    | ~ spl10_177 ),
    inference(unit_resulting_resolution,[],[f17744,f4654])).

fof(f17748,plain,
    ( ~ spl10_177
    | spl10_178
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f17432,f479,f295,f174,f17746,f17743])).

fof(f17746,plain,
    ( spl10_178
  <=> ! [X18,X19] : ~ r2_hidden(X19,k10_relat_1(sK4,k10_relat_1(sK4,X18))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_178])])).

fof(f17432,plain,
    ( ! [X19,X18] :
        ( ~ r2_hidden(X19,k10_relat_1(sK4,k10_relat_1(sK4,X18)))
        | ~ v1_xboole_0(k10_relat_1(sK4,u1_struct_0(sK2))) )
    | ~ spl10_4
    | ~ spl10_30
    | ~ spl10_56 ),
    inference(superposition,[],[f17037,f4049])).

fof(f17037,plain,
    ( ! [X92,X93,X91] :
        ( ~ r2_hidden(X93,k10_relat_1(sK4,k6_subset_1(X91,X92)))
        | ~ v1_xboole_0(k10_relat_1(sK4,X91)) )
    | ~ spl10_4
    | ~ spl10_56 ),
    inference(superposition,[],[f486,f16903])).

fof(f486,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X3,k6_subset_1(X2,X4))
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f147,f130])).

fof(f16210,plain,
    ( spl10_174
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6405,f295,f16208])).

fof(f16208,plain,
    ( spl10_174
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_174])])).

fof(f6405,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6294,f890])).

fof(f6294,plain,
    ( ! [X3] : r1_tarski(sK7(k1_zfmisc_1(k6_subset_1(sK4,X3))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6079,f907])).

fof(f6079,plain,
    ( ! [X0,X1] : r1_tarski(k6_subset_1(k6_subset_1(sK4,X0),X1),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f2106,f138])).

fof(f2106,plain,
    ( ! [X0,X1] : m1_subset_1(k6_subset_1(k6_subset_1(sK4,X0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(forward_demodulation,[],[f2085,f2087])).

fof(f2087,plain,
    ( ! [X0,X1] : k6_subset_1(k6_subset_1(sK4,X0),X1) = k7_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),k6_subset_1(sK4,X0),X1)
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1450,f155])).

fof(f1450,plain,
    ( ! [X0] : m1_subset_1(k6_subset_1(sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f1397,f741])).

fof(f741,plain,
    ( ! [X0] : m1_subset_1(k7_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK4,X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f142])).

fof(f1397,plain,
    ( ! [X0] : k6_subset_1(sK4,X0) = k7_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK4,X0)
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f155])).

fof(f2085,plain,
    ( ! [X0,X1] : m1_subset_1(k7_subset_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),k6_subset_1(sK4,X0),X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1450,f142])).

fof(f16191,plain,
    ( spl10_172
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6390,f295,f16189])).

fof(f16189,plain,
    ( spl10_172
  <=> r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_172])])).

fof(f6390,plain,
    ( r1_tarski(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6287,f878])).

fof(f6287,plain,
    ( ! [X3] : r1_tarski(k6_subset_1(sK7(k1_zfmisc_1(sK4)),X3),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6079,f907])).

fof(f16184,plain,
    ( spl10_170
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6381,f295,f16182])).

fof(f16182,plain,
    ( spl10_170
  <=> r1_tarski(k3_subset_1(k3_subset_1(sK4,sK4),k3_subset_1(sK4,sK4)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_170])])).

fof(f6381,plain,
    ( r1_tarski(k3_subset_1(k3_subset_1(sK4,sK4),k3_subset_1(sK4,sK4)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6284,f878])).

fof(f6284,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(k3_subset_1(sK4,sK4),X0),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6079,f878])).

fof(f14382,plain,
    ( spl10_168
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4241,f4191,f14380])).

fof(f14380,plain,
    ( spl10_168
  <=> r2_hidden(k3_subset_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))),sK7(k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_168])])).

fof(f4241,plain,
    ( r2_hidden(k3_subset_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))),sK7(k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f1704,f4192,f134])).

fof(f14067,plain,
    ( ~ spl10_167
    | ~ spl10_0
    | ~ spl10_30
    | spl10_151 ),
    inference(avatar_split_clause,[],[f14060,f6708,f295,f160,f14065])).

fof(f6708,plain,
    ( spl10_151
  <=> ~ v4_pre_topc(k10_relat_1(sK4,sK6(sK2,sK4,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_151])])).

fof(f14060,plain,
    ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(sK2),k10_relat_1(sK4,sK6(sK2,sK4,sK3))),sK2)
    | ~ spl10_0
    | ~ spl10_30
    | ~ spl10_151 ),
    inference(unit_resulting_resolution,[],[f6709,f8653])).

fof(f6709,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK4,sK6(sK2,sK4,sK3)),sK2)
    | ~ spl10_151 ),
    inference(avatar_component_clause,[],[f6708])).

fof(f12084,plain,
    ( ~ spl10_165
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4358,f4305,f12082])).

fof(f12082,plain,
    ( spl10_165
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_165])])).

fof(f4358,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f2291,f4306,f146])).

fof(f12070,plain,
    ( spl10_162
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4275,f4191,f12068])).

fof(f12068,plain,
    ( spl10_162
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_162])])).

fof(f4275,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f2291,f4192,f134])).

fof(f11387,plain,
    ( spl10_160
    | ~ spl10_146 ),
    inference(avatar_split_clause,[],[f6571,f6518,f11385])).

fof(f11385,plain,
    ( spl10_160
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_160])])).

fof(f6518,plain,
    ( spl10_146
  <=> r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_146])])).

fof(f6571,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_146 ),
    inference(unit_resulting_resolution,[],[f6519,f139])).

fof(f6519,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_146 ),
    inference(avatar_component_clause,[],[f6518])).

fof(f11380,plain,
    ( spl10_158
    | ~ spl10_144 ),
    inference(avatar_split_clause,[],[f6569,f6511,f11378])).

fof(f11378,plain,
    ( spl10_158
  <=> m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_158])])).

fof(f6511,plain,
    ( spl10_144
  <=> r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_144])])).

fof(f6569,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_144 ),
    inference(unit_resulting_resolution,[],[f6512,f139])).

fof(f6512,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_144 ),
    inference(avatar_component_clause,[],[f6511])).

fof(f10819,plain,
    ( ~ spl10_157
    | ~ spl10_2
    | spl10_121 ),
    inference(avatar_split_clause,[],[f10806,f5199,f167,f10817])).

fof(f5199,plain,
    ( spl10_121
  <=> ~ v3_pre_topc(u1_struct_0(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_121])])).

fof(f10806,plain,
    ( ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK3),u1_struct_0(sK3)),sK3)
    | ~ spl10_2
    | ~ spl10_121 ),
    inference(unit_resulting_resolution,[],[f168,f5200,f225,f126])).

fof(f5200,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | ~ spl10_121 ),
    inference(avatar_component_clause,[],[f5199])).

fof(f10523,plain,
    ( spl10_154
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6179,f295,f10521])).

fof(f10521,plain,
    ( spl10_154
  <=> v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_154])])).

fof(f6179,plain,
    ( v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4)))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6119,f878])).

fof(f6119,plain,
    ( ! [X8] : v1_relat_1(k6_subset_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),X8))
    | ~ spl10_30 ),
    inference(superposition,[],[f6076,f890])).

fof(f6076,plain,
    ( ! [X0,X1] : v1_relat_1(k6_subset_1(k6_subset_1(sK4,X0),X1))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f2106,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',cc1_relset_1)).

fof(f7192,plain,
    ( ~ spl10_153
    | spl10_61 ),
    inference(avatar_split_clause,[],[f503,f500,f7190])).

fof(f7190,plain,
    ( spl10_153
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK7(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_153])])).

fof(f500,plain,
    ( spl10_61
  <=> ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_61])])).

fof(f503,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK7(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_61 ),
    inference(unit_resulting_resolution,[],[f501,f363])).

fof(f501,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_61 ),
    inference(avatar_component_clause,[],[f500])).

fof(f6710,plain,
    ( spl10_148
    | ~ spl10_151
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6365,f295,f6708,f6702])).

fof(f6365,plain,
    ( ~ v4_pre_topc(k10_relat_1(sK4,sK6(sK2,sK4,sK3)),sK2)
    | sP0(sK2,sK4,sK3)
    | ~ spl10_30 ),
    inference(superposition,[],[f123,f3662])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X2),X1,sK6(X0,X1,X2)),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f6520,plain,
    ( spl10_146
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6393,f295,f6518])).

fof(f6393,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6287,f907])).

fof(f6513,plain,
    ( spl10_144
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6384,f295,f6511])).

fof(f6384,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6284,f907])).

fof(f6281,plain,
    ( spl10_142
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6140,f295,f6279])).

fof(f6279,plain,
    ( spl10_142
  <=> v1_relat_1(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_142])])).

fof(f6140,plain,
    ( v1_relat_1(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4))))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6116,f890])).

fof(f6116,plain,
    ( ! [X3] : v1_relat_1(k6_subset_1(sK7(k1_zfmisc_1(sK4)),X3))
    | ~ spl10_30 ),
    inference(superposition,[],[f6076,f907])).

fof(f6264,plain,
    ( spl10_140
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6133,f295,f6262])).

fof(f6262,plain,
    ( spl10_140
  <=> v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK4),sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_140])])).

fof(f6133,plain,
    ( v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK4),sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4)))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6113,f890])).

fof(f6113,plain,
    ( ! [X0] : v1_relat_1(k6_subset_1(k3_subset_1(sK4,sK4),X0))
    | ~ spl10_30 ),
    inference(superposition,[],[f6076,f878])).

fof(f6223,plain,
    ( spl10_138
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6147,f295,f6221])).

fof(f6221,plain,
    ( spl10_138
  <=> v1_relat_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_138])])).

fof(f6147,plain,
    ( v1_relat_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6123,f890])).

fof(f6123,plain,
    ( ! [X3] : v1_relat_1(sK7(k1_zfmisc_1(k6_subset_1(sK4,X3))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6076,f907])).

fof(f6206,plain,
    ( spl10_136
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6134,f295,f6204])).

fof(f6204,plain,
    ( spl10_136
  <=> v1_relat_1(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_136])])).

fof(f6134,plain,
    ( v1_relat_1(k3_subset_1(sK7(k1_zfmisc_1(sK4)),sK7(k1_zfmisc_1(sK4))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6116,f878])).

fof(f6199,plain,
    ( spl10_134
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6127,f295,f6197])).

fof(f6197,plain,
    ( spl10_134
  <=> v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK4),k3_subset_1(sK4,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_134])])).

fof(f6127,plain,
    ( v1_relat_1(k3_subset_1(k3_subset_1(sK4,sK4),k3_subset_1(sK4,sK4)))
    | ~ spl10_30 ),
    inference(superposition,[],[f6113,f878])).

fof(f6161,plain,
    ( spl10_132
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6137,f295,f6159])).

fof(f6159,plain,
    ( spl10_132
  <=> v1_relat_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_132])])).

fof(f6137,plain,
    ( v1_relat_1(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(sK4)))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6116,f907])).

fof(f6154,plain,
    ( spl10_130
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f6130,f295,f6152])).

fof(f6152,plain,
    ( spl10_130
  <=> v1_relat_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_130])])).

fof(f6130,plain,
    ( v1_relat_1(sK7(k1_zfmisc_1(k3_subset_1(sK4,sK4))))
    | ~ spl10_30 ),
    inference(superposition,[],[f6113,f907])).

fof(f6073,plain,
    ( spl10_128
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2105,f295,f6071])).

fof(f6071,plain,
    ( spl10_128
  <=> m1_subset_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_128])])).

fof(f2105,plain,
    ( m1_subset_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(superposition,[],[f1450,f890])).

fof(f6020,plain,
    ( spl10_126
    | spl10_61 ),
    inference(avatar_split_clause,[],[f505,f500,f6018])).

fof(f6018,plain,
    ( spl10_126
  <=> r2_hidden(sK7(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_126])])).

fof(f505,plain,
    ( r2_hidden(sK7(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_61 ),
    inference(unit_resulting_resolution,[],[f129,f501,f134])).

fof(f5886,plain,
    ( ~ spl10_125
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4370,f4305,f5884])).

fof(f5884,plain,
    ( spl10_125
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_125])])).

fof(f4370,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f4306,f1860])).

fof(f5681,plain,
    ( spl10_122
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4264,f4191,f5679])).

fof(f5679,plain,
    ( spl10_122
  <=> r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_122])])).

fof(f4264,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f1683,f4192,f134])).

fof(f5201,plain,
    ( spl10_118
    | ~ spl10_121
    | spl10_19
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f5142,f295,f231,f5199,f5193])).

fof(f5193,plain,
    ( spl10_118
  <=> v3_pre_topc(k10_relat_1(sK4,u1_struct_0(sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_118])])).

fof(f5142,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK3),sK3)
    | v3_pre_topc(k10_relat_1(sK4,u1_struct_0(sK3)),sK2)
    | ~ spl10_19
    | ~ spl10_30 ),
    inference(resolution,[],[f3734,f225])).

fof(f4983,plain,
    ( ~ spl10_117
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4219,f4191,f4981])).

fof(f4981,plain,
    ( spl10_117
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_117])])).

fof(f4219,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f4192,f1044])).

fof(f4920,plain,
    ( spl10_114
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4234,f4191,f4918])).

fof(f4918,plain,
    ( spl10_114
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_114])])).

fof(f4234,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK2),sK7(k1_zfmisc_1(u1_struct_0(sK2)))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f516,f4192,f134])).

fof(f4630,plain,
    ( ~ spl10_113
    | spl10_101 ),
    inference(avatar_split_clause,[],[f4368,f4305,f4628])).

fof(f4628,plain,
    ( spl10_113
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_113])])).

fof(f4368,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))))
    | ~ spl10_101 ),
    inference(unit_resulting_resolution,[],[f4306,f1813])).

fof(f4614,plain,
    ( spl10_110
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4272,f4191,f4612])).

fof(f4612,plain,
    ( spl10_110
  <=> r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_110])])).

fof(f4272,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(sK7(k1_zfmisc_1(u1_struct_0(sK2))))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f1660,f4192,f134])).

fof(f4481,plain,
    ( ~ spl10_109
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4217,f4191,f4479])).

fof(f4479,plain,
    ( spl10_109
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_109])])).

fof(f4217,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f4192,f571])).

fof(f4424,plain,
    ( spl10_106
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4228,f4191,f4422])).

fof(f4422,plain,
    ( spl10_106
  <=> r2_hidden(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_106])])).

fof(f4228,plain,
    ( r2_hidden(k3_subset_1(u1_struct_0(sK2),u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f513,f4192,f134])).

fof(f4408,plain,
    ( spl10_104
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4276,f4191,f4406])).

fof(f4406,plain,
    ( spl10_104
  <=> r2_hidden(sK7(k1_zfmisc_1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_104])])).

fof(f4276,plain,
    ( r2_hidden(sK7(k1_zfmisc_1(u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f129,f4192,f134])).

fof(f4385,plain,
    ( ~ spl10_103
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4225,f4191,f4383])).

fof(f4383,plain,
    ( spl10_103
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_103])])).

fof(f4225,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),sK7(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f4192,f363])).

fof(f4307,plain,
    ( ~ spl10_101
    | spl10_49
    | spl10_99 ),
    inference(avatar_split_clause,[],[f4300,f4297,f415,f4305])).

fof(f4297,plain,
    ( spl10_99
  <=> ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_99])])).

fof(f4300,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_49
    | ~ spl10_99 ),
    inference(unit_resulting_resolution,[],[f416,f4298,f134])).

fof(f4298,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_99 ),
    inference(avatar_component_clause,[],[f4297])).

fof(f4299,plain,
    ( ~ spl10_99
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4212,f4191,f4297])).

fof(f4212,plain,
    ( ~ r2_hidden(k1_zfmisc_1(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f4192,f462])).

fof(f4283,plain,
    ( spl10_96
    | spl10_93 ),
    inference(avatar_split_clause,[],[f4227,f4191,f4281])).

fof(f4281,plain,
    ( spl10_96
  <=> r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_96])])).

fof(f4227,plain,
    ( r2_hidden(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_93 ),
    inference(unit_resulting_resolution,[],[f225,f4192,f134])).

fof(f4209,plain,
    ( ~ spl10_93
    | ~ spl10_94 ),
    inference(avatar_split_clause,[],[f4205,f4197,f4191])).

fof(f4205,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl10_94 ),
    inference(unit_resulting_resolution,[],[f4198,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',t7_boole)).

fof(f4199,plain,
    ( spl10_92
    | spl10_94
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f3742,f295,f4197,f4194])).

fof(f4194,plain,
    ( spl10_92
  <=> v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_92])])).

fof(f3742,plain,
    ( ! [X12] :
        ( r2_hidden(k10_relat_1(sK4,X12),k1_zfmisc_1(u1_struct_0(sK2)))
        | v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl10_30 ),
    inference(backward_demodulation,[],[f3662,f3334])).

fof(f3334,plain,
    ( ! [X12] :
        ( v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK2)))
        | r2_hidden(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4,X12),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl10_30 ),
    inference(resolution,[],[f1935,f134])).

fof(f3386,plain,
    ( spl10_90
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2154,f295,f3384])).

fof(f3384,plain,
    ( spl10_90
  <=> r1_tarski(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_90])])).

fof(f2154,plain,
    ( r1_tarski(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f2084,f890])).

fof(f2084,plain,
    ( ! [X0] : r1_tarski(k6_subset_1(sK4,X0),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1450,f138])).

fof(f2608,plain,
    ( spl10_88
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2102,f295,f2606])).

fof(f2606,plain,
    ( spl10_88
  <=> m1_subset_1(sK7(k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_88])])).

fof(f2102,plain,
    ( m1_subset_1(sK7(k1_zfmisc_1(sK4)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(superposition,[],[f1450,f907])).

fof(f2601,plain,
    ( spl10_86
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2099,f295,f2599])).

fof(f2599,plain,
    ( spl10_86
  <=> m1_subset_1(k3_subset_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_86])])).

fof(f2099,plain,
    ( m1_subset_1(k3_subset_1(sK4,sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl10_30 ),
    inference(superposition,[],[f1450,f878])).

fof(f2168,plain,
    ( spl10_84
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2151,f295,f2166])).

fof(f2166,plain,
    ( spl10_84
  <=> r1_tarski(sK7(k1_zfmisc_1(sK4)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_84])])).

fof(f2151,plain,
    ( r1_tarski(sK7(k1_zfmisc_1(sK4)),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f2084,f907])).

fof(f2161,plain,
    ( spl10_82
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2148,f295,f2159])).

fof(f2159,plain,
    ( spl10_82
  <=> r1_tarski(k3_subset_1(sK4,sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_82])])).

fof(f2148,plain,
    ( r1_tarski(k3_subset_1(sK4,sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(superposition,[],[f2084,f878])).

fof(f2145,plain,
    ( spl10_80
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2114,f295,f2143])).

fof(f2143,plain,
    ( spl10_80
  <=> v1_relat_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_80])])).

fof(f2114,plain,
    ( v1_relat_1(k3_subset_1(sK4,sK7(k1_zfmisc_1(sK4))))
    | ~ spl10_30 ),
    inference(superposition,[],[f2081,f890])).

fof(f2081,plain,
    ( ! [X0] : v1_relat_1(k6_subset_1(sK4,X0))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f1450,f144])).

fof(f2128,plain,
    ( spl10_78
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2111,f295,f2126])).

fof(f2126,plain,
    ( spl10_78
  <=> v1_relat_1(sK7(k1_zfmisc_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_78])])).

fof(f2111,plain,
    ( v1_relat_1(sK7(k1_zfmisc_1(sK4)))
    | ~ spl10_30 ),
    inference(superposition,[],[f2081,f907])).

fof(f2121,plain,
    ( spl10_76
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f2108,f295,f2119])).

fof(f2119,plain,
    ( spl10_76
  <=> v1_relat_1(k3_subset_1(sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_76])])).

fof(f2108,plain,
    ( v1_relat_1(k3_subset_1(sK4,sK4))
    | ~ spl10_30 ),
    inference(superposition,[],[f2081,f878])).

fof(f1092,plain,
    ( spl10_74
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(avatar_split_clause,[],[f1084,f1076,f949,f1090])).

fof(f1090,plain,
    ( spl10_74
  <=> k1_xboole_0 = sK7(k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_74])])).

fof(f1076,plain,
    ( spl10_72
  <=> k1_xboole_0 = k3_subset_1(k1_xboole_0,sK7(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_72])])).

fof(f1084,plain,
    ( k1_xboole_0 = sK7(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_70
    | ~ spl10_72 ),
    inference(forward_demodulation,[],[f1079,f950])).

fof(f1079,plain,
    ( k3_subset_1(k1_xboole_0,k1_xboole_0) = sK7(k1_zfmisc_1(k1_xboole_0))
    | ~ spl10_72 ),
    inference(superposition,[],[f635,f1077])).

fof(f1077,plain,
    ( k1_xboole_0 = k3_subset_1(k1_xboole_0,sK7(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl10_72 ),
    inference(avatar_component_clause,[],[f1076])).

fof(f1078,plain,(
    spl10_72 ),
    inference(avatar_split_clause,[],[f1039,f1076])).

fof(f1039,plain,(
    k1_xboole_0 = k3_subset_1(k1_xboole_0,sK7(k1_zfmisc_1(k1_xboole_0))) ),
    inference(superposition,[],[f890,f153])).

fof(f951,plain,(
    spl10_70 ),
    inference(avatar_split_clause,[],[f915,f949])).

fof(f915,plain,(
    k1_xboole_0 = k3_subset_1(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f878,f152])).

fof(f627,plain,
    ( ~ spl10_69
    | ~ spl10_66 ),
    inference(avatar_split_clause,[],[f616,f609,f625])).

fof(f625,plain,
    ( spl10_69
  <=> ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK7(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_69])])).

fof(f609,plain,
    ( spl10_66
  <=> r2_hidden(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_66])])).

fof(f616,plain,
    ( ~ r2_hidden(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)),sK7(sK4))
    | ~ spl10_66 ),
    inference(unit_resulting_resolution,[],[f610,f132])).

fof(f610,plain,
    ( r2_hidden(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_66 ),
    inference(avatar_component_clause,[],[f609])).

fof(f611,plain,
    ( spl10_66
    | spl10_61
    | ~ spl10_64 ),
    inference(avatar_split_clause,[],[f603,f600,f500,f609])).

fof(f600,plain,
    ( spl10_64
  <=> m1_subset_1(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_64])])).

fof(f603,plain,
    ( r2_hidden(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_61
    | ~ spl10_64 ),
    inference(unit_resulting_resolution,[],[f501,f601,f134])).

fof(f601,plain,
    ( m1_subset_1(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_64 ),
    inference(avatar_component_clause,[],[f600])).

fof(f602,plain,
    ( spl10_62
    | spl10_64
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f589,f295,f600,f594])).

fof(f594,plain,
    ( spl10_62
  <=> v1_xboole_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_62])])).

fof(f589,plain,
    ( m1_subset_1(sK7(sK4),k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | v1_xboole_0(sK4)
    | ~ spl10_30 ),
    inference(resolution,[],[f582,f360])).

fof(f582,plain,
    ( ! [X14] :
        ( ~ r2_hidden(X14,sK4)
        | m1_subset_1(X14,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) )
    | ~ spl10_30 ),
    inference(resolution,[],[f146,f296])).

fof(f502,plain,
    ( spl10_58
    | ~ spl10_61
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f487,f295,f500,f494])).

fof(f494,plain,
    ( spl10_58
  <=> ! [X5] : ~ r2_hidden(X5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_58])])).

fof(f487,plain,
    ( ! [X5] :
        ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
        | ~ r2_hidden(X5,sK4) )
    | ~ spl10_30 ),
    inference(resolution,[],[f147,f296])).

fof(f481,plain,
    ( spl10_56
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f469,f295,f479])).

fof(f469,plain,
    ( v1_relat_1(sK4)
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f144])).

fof(f458,plain,
    ( ~ spl10_55
    | ~ spl10_50 ),
    inference(avatar_split_clause,[],[f438,f433,f456])).

fof(f456,plain,
    ( spl10_55
  <=> ~ r2_hidden(u1_struct_0(sK2),sK7(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_55])])).

fof(f433,plain,
    ( spl10_50
  <=> r2_hidden(sK7(u1_struct_0(sK2)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_50])])).

fof(f438,plain,
    ( ~ r2_hidden(u1_struct_0(sK2),sK7(u1_struct_0(sK2)))
    | ~ spl10_50 ),
    inference(unit_resulting_resolution,[],[f434,f132])).

fof(f434,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_50 ),
    inference(avatar_component_clause,[],[f433])).

fof(f451,plain,
    ( ~ spl10_53
    | ~ spl10_42 ),
    inference(avatar_split_clause,[],[f424,f369,f449])).

fof(f449,plain,
    ( spl10_53
  <=> ~ r2_hidden(u1_struct_0(sK3),sK7(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_53])])).

fof(f369,plain,
    ( spl10_42
  <=> r2_hidden(sK7(u1_struct_0(sK3)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_42])])).

fof(f424,plain,
    ( ~ r2_hidden(u1_struct_0(sK3),sK7(u1_struct_0(sK3)))
    | ~ spl10_42 ),
    inference(unit_resulting_resolution,[],[f370,f132])).

fof(f370,plain,
    ( r2_hidden(sK7(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_42 ),
    inference(avatar_component_clause,[],[f369])).

fof(f435,plain,
    ( spl10_50
    | spl10_49 ),
    inference(avatar_split_clause,[],[f419,f415,f433])).

fof(f419,plain,
    ( r2_hidden(sK7(u1_struct_0(sK2)),u1_struct_0(sK2))
    | ~ spl10_49 ),
    inference(unit_resulting_resolution,[],[f129,f416,f134])).

fof(f417,plain,
    ( ~ spl10_49
    | spl10_35 ),
    inference(avatar_split_clause,[],[f410,f305,f415])).

fof(f305,plain,
    ( spl10_35
  <=> u1_struct_0(sK2) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_35])])).

fof(f410,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ spl10_35 ),
    inference(unit_resulting_resolution,[],[f306,f112])).

fof(f306,plain,
    ( u1_struct_0(sK2) != k1_xboole_0
    | ~ spl10_35 ),
    inference(avatar_component_clause,[],[f305])).

fof(f405,plain,
    ( spl10_46
    | ~ spl10_24
    | ~ spl10_34 ),
    inference(avatar_split_clause,[],[f374,f308,f260,f403])).

fof(f308,plain,
    ( spl10_34
  <=> u1_struct_0(sK2) = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_34])])).

fof(f374,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | ~ spl10_24
    | ~ spl10_34 ),
    inference(backward_demodulation,[],[f309,f261])).

fof(f309,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | ~ spl10_34 ),
    inference(avatar_component_clause,[],[f308])).

fof(f396,plain,
    ( ~ spl10_37
    | spl10_39 ),
    inference(avatar_split_clause,[],[f328,f325,f318])).

fof(f325,plain,
    ( spl10_39
  <=> u1_struct_0(sK3) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f328,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl10_39 ),
    inference(unit_resulting_resolution,[],[f326,f112])).

fof(f326,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | ~ spl10_39 ),
    inference(avatar_component_clause,[],[f325])).

fof(f395,plain,
    ( spl10_44
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36 ),
    inference(avatar_split_clause,[],[f381,f315,f299,f267,f393])).

fof(f315,plain,
    ( spl10_36
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f381,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl10_26
    | ~ spl10_32
    | ~ spl10_36 ),
    inference(backward_demodulation,[],[f380,f316])).

fof(f316,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f315])).

fof(f371,plain,
    ( spl10_42
    | spl10_37 ),
    inference(avatar_split_clause,[],[f356,f318,f369])).

fof(f356,plain,
    ( r2_hidden(sK7(u1_struct_0(sK3)),u1_struct_0(sK3))
    | ~ spl10_37 ),
    inference(unit_resulting_resolution,[],[f319,f129,f134])).

fof(f337,plain,
    ( spl10_40
    | ~ spl10_30 ),
    inference(avatar_split_clause,[],[f329,f295,f335])).

fof(f335,plain,
    ( spl10_40
  <=> r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f329,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))
    | ~ spl10_30 ),
    inference(unit_resulting_resolution,[],[f296,f138])).

fof(f327,plain,
    ( ~ spl10_39
    | ~ spl10_26
    | spl10_33 ),
    inference(avatar_split_clause,[],[f312,f302,f267,f325])).

fof(f312,plain,
    ( u1_struct_0(sK3) != k1_xboole_0
    | ~ spl10_26
    | ~ spl10_33 ),
    inference(superposition,[],[f303,f268])).

fof(f320,plain,
    ( ~ spl10_37
    | ~ spl10_26
    | spl10_33 ),
    inference(avatar_split_clause,[],[f313,f302,f267,f318])).

fof(f313,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ spl10_26
    | ~ spl10_33 ),
    inference(forward_demodulation,[],[f311,f268])).

fof(f311,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK3))
    | ~ spl10_33 ),
    inference(unit_resulting_resolution,[],[f303,f112])).

fof(f310,plain,
    ( ~ spl10_33
    | spl10_34
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f248,f201,f308,f302])).

fof(f248,plain,
    ( u1_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK3) != k1_xboole_0
    | ~ spl10_10 ),
    inference(backward_demodulation,[],[f240,f105])).

fof(f105,plain,
    ( k2_struct_0(sK2) = k1_xboole_0
    | k2_struct_0(sK3) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f84])).

fof(f240,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl10_10 ),
    inference(unit_resulting_resolution,[],[f202,f113])).

fof(f113,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',d3_struct_0)).

fof(f297,plain,(
    spl10_30 ),
    inference(avatar_split_clause,[],[f104,f295])).

fof(f104,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f84])).

fof(f276,plain,
    ( spl10_28
    | ~ spl10_14 ),
    inference(avatar_split_clause,[],[f243,f215,f274])).

fof(f274,plain,
    ( spl10_28
  <=> u1_struct_0(sK9) = k2_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_28])])).

fof(f215,plain,
    ( spl10_14
  <=> l1_struct_0(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f243,plain,
    ( u1_struct_0(sK9) = k2_struct_0(sK9)
    | ~ spl10_14 ),
    inference(unit_resulting_resolution,[],[f216,f113])).

fof(f216,plain,
    ( l1_struct_0(sK9)
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f215])).

fof(f269,plain,
    ( spl10_26
    | ~ spl10_12 ),
    inference(avatar_split_clause,[],[f241,f208,f267])).

fof(f241,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl10_12 ),
    inference(unit_resulting_resolution,[],[f209,f113])).

fof(f262,plain,
    ( spl10_24
    | ~ spl10_10 ),
    inference(avatar_split_clause,[],[f240,f201,f260])).

fof(f255,plain,
    ( spl10_22
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f242,f181,f253])).

fof(f253,plain,
    ( spl10_22
  <=> u1_struct_0(sK8) = k2_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f181,plain,
    ( spl10_6
  <=> l1_struct_0(sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f242,plain,
    ( u1_struct_0(sK8) = k2_struct_0(sK8)
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f182,f113])).

fof(f182,plain,
    ( l1_struct_0(sK8)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f181])).

fof(f239,plain,
    ( ~ spl10_19
    | spl10_20 ),
    inference(avatar_split_clause,[],[f108,f237,f231])).

fof(f108,plain,
    ( v3_pre_topc(sK5,sK3)
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f224,plain,(
    spl10_16 ),
    inference(avatar_split_clause,[],[f103,f222])).

fof(f103,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f84])).

fof(f217,plain,
    ( spl10_14
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f193,f188,f215])).

fof(f188,plain,
    ( spl10_8
  <=> l1_pre_topc(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f193,plain,
    ( l1_struct_0(sK9)
    | ~ spl10_8 ),
    inference(unit_resulting_resolution,[],[f189,f117])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',dt_l1_pre_topc)).

fof(f189,plain,
    ( l1_pre_topc(sK9)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f188])).

fof(f210,plain,
    ( spl10_12
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f192,f167,f208])).

fof(f192,plain,
    ( l1_struct_0(sK3)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f168,f117])).

fof(f203,plain,
    ( spl10_10
    | ~ spl10_0 ),
    inference(avatar_split_clause,[],[f191,f160,f201])).

fof(f191,plain,
    ( l1_struct_0(sK2)
    | ~ spl10_0 ),
    inference(unit_resulting_resolution,[],[f161,f117])).

fof(f190,plain,(
    spl10_8 ),
    inference(avatar_split_clause,[],[f151,f188])).

fof(f151,plain,(
    l1_pre_topc(sK9) ),
    inference(cnf_transformation,[],[f99])).

fof(f99,plain,(
    l1_pre_topc(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f21,f98])).

fof(f98,plain,
    ( ? [X0] : l1_pre_topc(X0)
   => l1_pre_topc(sK9) ),
    introduced(choice_axiom,[])).

fof(f21,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',existence_l1_pre_topc)).

fof(f183,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f150,f181])).

fof(f150,plain,(
    l1_struct_0(sK8) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    l1_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f22,f96])).

fof(f96,plain,
    ( ? [X0] : l1_struct_0(X0)
   => l1_struct_0(sK8) ),
    introduced(choice_axiom,[])).

fof(f22,axiom,(
    ? [X0] : l1_struct_0(X0) ),
    file('/export/starexec/sandbox/benchmark/tops_2__t55_tops_2.p',existence_l1_struct_0)).

fof(f176,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f102,f174])).

fof(f102,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

fof(f169,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f101,f167])).

fof(f101,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f84])).

fof(f162,plain,(
    spl10_0 ),
    inference(avatar_split_clause,[],[f100,f160])).

fof(f100,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f84])).
%------------------------------------------------------------------------------
