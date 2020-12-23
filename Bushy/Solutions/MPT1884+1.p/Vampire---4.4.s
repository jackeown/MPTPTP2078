%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tex_2__t52_tex_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:38:53 EDT 2019

% Result     : Theorem 2.79s
% Output     : Refutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :  490 (1230 expanded)
%              Number of leaves         :   93 ( 499 expanded)
%              Depth                    :   15
%              Number of atoms          : 2326 (7144 expanded)
%              Number of equality atoms :  205 ( 734 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f184,f191,f198,f205,f275,f288,f312,f323,f511,f527,f598,f609,f697,f720,f927,f940,f1100,f1123,f1314,f1323,f1326,f1336,f1374,f1398,f1443,f1483,f1535,f1658,f1671,f1677,f1764,f1950,f2219,f2437,f2859,f3094,f4116,f5703,f6711,f6844,f6898,f9283,f9297,f18705,f18732,f18877,f19045,f19700,f20725,f22481,f26598,f26824,f30200,f30208,f46596,f49849,f49856,f49983,f50074,f50408,f51199,f55889,f55940,f56108])).

fof(f56108,plain,
    ( spl12_1640
    | ~ spl12_278
    | ~ spl12_3344
    | ~ spl12_3346 ),
    inference(avatar_split_clause,[],[f55988,f55938,f55887,f2217,f20386])).

fof(f20386,plain,
    ( spl12_1640
  <=> u1_struct_0(sK1) = sK4(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1640])])).

fof(f2217,plain,
    ( spl12_278
  <=> u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_278])])).

fof(f55887,plain,
    ( spl12_3344
  <=> ! [X7,X6] :
        ( u1_struct_0(sK6(sK0,u1_struct_0(sK1))) = X6
        | g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3344])])).

fof(f55938,plain,
    ( spl12_3346
  <=> g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))) = sK6(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3346])])).

fof(f55988,plain,
    ( u1_struct_0(sK1) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl12_278
    | ~ spl12_3344
    | ~ spl12_3346 ),
    inference(forward_demodulation,[],[f55978,f2218])).

fof(f2218,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_278 ),
    inference(avatar_component_clause,[],[f2217])).

fof(f55978,plain,
    ( u1_struct_0(sK6(sK0,u1_struct_0(sK1))) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl12_3344
    | ~ spl12_3346 ),
    inference(trivial_inequality_removal,[],[f55977])).

fof(f55977,plain,
    ( sK6(sK0,u1_struct_0(sK1)) != sK6(sK0,u1_struct_0(sK1))
    | u1_struct_0(sK6(sK0,u1_struct_0(sK1))) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl12_3344
    | ~ spl12_3346 ),
    inference(superposition,[],[f55888,f55939])).

fof(f55939,plain,
    ( g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_3346 ),
    inference(avatar_component_clause,[],[f55938])).

fof(f55888,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK6(sK0,u1_struct_0(sK1))) = X6 )
    | ~ spl12_3344 ),
    inference(avatar_component_clause,[],[f55887])).

fof(f55940,plain,
    ( spl12_3346
    | ~ spl12_3132
    | ~ spl12_3210 ),
    inference(avatar_split_clause,[],[f54949,f51197,f49847,f55938])).

fof(f49847,plain,
    ( spl12_3132
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK6(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3132])])).

fof(f51197,plain,
    ( spl12_3210
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3210])])).

fof(f54949,plain,
    ( g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_3132
    | ~ spl12_3210 ),
    inference(forward_demodulation,[],[f51198,f49848])).

fof(f49848,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_3132 ),
    inference(avatar_component_clause,[],[f49847])).

fof(f51198,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | ~ spl12_3210 ),
    inference(avatar_component_clause,[],[f51197])).

fof(f55889,plain,
    ( spl12_3344
    | ~ spl12_3132
    | ~ spl12_3152 ),
    inference(avatar_split_clause,[],[f54678,f49981,f49847,f55887])).

fof(f49981,plain,
    ( spl12_3152
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3152])])).

fof(f54678,plain,
    ( ! [X6,X7] :
        ( u1_struct_0(sK6(sK0,u1_struct_0(sK1))) = X6
        | g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1)) )
    | ~ spl12_3132
    | ~ spl12_3152 ),
    inference(backward_demodulation,[],[f49848,f49982])).

fof(f49982,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 )
    | ~ spl12_3152 ),
    inference(avatar_component_clause,[],[f49981])).

fof(f51199,plain,
    ( ~ spl12_2037
    | spl12_3210
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_148
    | spl12_1509
    | ~ spl12_1510
    | ~ spl12_1524
    | spl12_1851 ),
    inference(avatar_split_clause,[],[f50423,f23205,f19043,f18875,f18866,f1289,f925,f695,f604,f196,f189,f182,f51197,f26814])).

fof(f26814,plain,
    ( spl12_2037
  <=> ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2037])])).

fof(f182,plain,
    ( spl12_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1])])).

fof(f189,plain,
    ( spl12_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f196,plain,
    ( spl12_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f604,plain,
    ( spl12_79
  <=> ~ v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_79])])).

fof(f695,plain,
    ( spl12_84
  <=> v2_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_84])])).

fof(f925,plain,
    ( spl12_114
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_114])])).

fof(f1289,plain,
    ( spl12_148
  <=> ! [X1,X0] :
        ( v1_xboole_0(sK4(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_tex_2(X1,X0)
        | ~ v2_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,sK6(X0,sK4(X0,X1)))
        | ~ m1_pre_topc(sK6(X0,sK4(X0,X1)),sK0)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(X0,sK4(X0,X1))),u1_pre_topc(sK6(X0,sK4(X0,X1))))
        | v2_struct_0(sK6(X0,sK4(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_148])])).

fof(f18866,plain,
    ( spl12_1509
  <=> ~ v1_xboole_0(sK4(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1509])])).

fof(f18875,plain,
    ( spl12_1510
  <=> m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1510])])).

fof(f19043,plain,
    ( spl12_1524
  <=> u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) = sK4(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1524])])).

fof(f23205,plain,
    ( spl12_1851
  <=> ~ v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1851])])).

fof(f50423,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(sK4(sK0,u1_struct_0(sK1)),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_148
    | ~ spl12_1509
    | ~ spl12_1510
    | ~ spl12_1524
    | ~ spl12_1851 ),
    inference(forward_demodulation,[],[f50422,f19044])).

fof(f19044,plain,
    ( u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl12_1524 ),
    inference(avatar_component_clause,[],[f19043])).

fof(f50422,plain,
    ( ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_148
    | ~ spl12_1509
    | ~ spl12_1510
    | ~ spl12_1851 ),
    inference(subsumption_resolution,[],[f50421,f23206])).

fof(f23206,plain,
    ( ~ v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1851 ),
    inference(avatar_component_clause,[],[f23205])).

fof(f50421,plain,
    ( ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_148
    | ~ spl12_1509
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50420,f18867])).

fof(f18867,plain,
    ( ~ v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_1509 ),
    inference(avatar_component_clause,[],[f18866])).

fof(f50420,plain,
    ( ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50419,f926])).

fof(f926,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_114 ),
    inference(avatar_component_clause,[],[f925])).

fof(f50419,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50418,f696])).

fof(f696,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_84 ),
    inference(avatar_component_clause,[],[f695])).

fof(f50418,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50417,f605])).

fof(f605,plain,
    ( ~ v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_79 ),
    inference(avatar_component_clause,[],[f604])).

fof(f50417,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50416,f183])).

fof(f183,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl12_1 ),
    inference(avatar_component_clause,[],[f182])).

fof(f50416,plain,
    ( v2_struct_0(sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50415,f190])).

fof(f190,plain,
    ( v2_pre_topc(sK0)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f189])).

fof(f50415,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_4
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(subsumption_resolution,[],[f50412,f197])).

fof(f197,plain,
    ( l1_pre_topc(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f196])).

fof(f50412,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))),u1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))))
    | v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_148
    | ~ spl12_1510 ),
    inference(resolution,[],[f1290,f18876])).

fof(f18876,plain,
    ( m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),sK0)
    | ~ spl12_1510 ),
    inference(avatar_component_clause,[],[f18875])).

fof(f1290,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK6(X0,sK4(X0,X1)),sK0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_tex_2(X1,X0)
        | ~ v2_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,sK6(X0,sK4(X0,X1)))
        | v1_xboole_0(sK4(X0,X1))
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(X0,sK4(X0,X1))),u1_pre_topc(sK6(X0,sK4(X0,X1))))
        | v2_struct_0(sK6(X0,sK4(X0,X1))) )
    | ~ spl12_148 ),
    inference(avatar_component_clause,[],[f1289])).

fof(f50408,plain,
    ( spl12_148
    | ~ spl12_68 ),
    inference(avatar_split_clause,[],[f50234,f509,f1289])).

fof(f509,plain,
    ( spl12_68
  <=> ! [X3] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_tdlat_3(X3)
        | v2_struct_0(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_68])])).

fof(f50234,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(sK1,sK6(X0,sK4(X0,X1)))
        | ~ m1_pre_topc(sK6(X0,sK4(X0,X1)),sK0)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(sK6(X0,sK4(X0,X1))),u1_pre_topc(sK6(X0,sK4(X0,X1))))
        | v2_struct_0(sK6(X0,sK4(X0,X1)))
        | v1_xboole_0(sK4(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v3_tex_2(X1,X0)
        | ~ v2_tex_2(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl12_68 ),
    inference(resolution,[],[f510,f438])).

fof(f438,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK6(X0,sK4(X0,X1)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f437,f132])).

fof(f132,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK4(X0,X1) != X1
                & r1_tarski(X1,sK4(X0,X1))
                & v2_tex_2(sK4(X0,X1),X0)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f88,f89])).

fof(f89,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) != X1
        & r1_tarski(X1,sK4(X0,X1))
        & v2_tex_2(sK4(X0,X1),X0)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f86])).

fof(f86,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',d7_tex_2)).

fof(f437,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK6(X0,sK4(X0,X1)))
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f436])).

fof(f436,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK6(X0,sK4(X0,X1)))
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f142,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK4(X0,X1),X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK6(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_struct_0(sK6(X0,X1)) = X1
            & m1_pre_topc(sK6(X0,X1),X0)
            & v1_tdlat_3(sK6(X0,X1))
            & v1_pre_topc(sK6(X0,X1))
            & ~ v2_struct_0(sK6(X0,X1)) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f59,f93])).

fof(f93,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( u1_struct_0(X2) = X1
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & v1_pre_topc(X2)
          & ~ v2_struct_0(X2) )
     => ( u1_struct_0(sK6(X0,X1)) = X1
        & m1_pre_topc(sK6(X0,X1),X0)
        & v1_tdlat_3(sK6(X0,X1))
        & v1_pre_topc(sK6(X0,X1))
        & ~ v2_struct_0(sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t34_tex_2)).

fof(f510,plain,
    ( ! [X3] :
        ( ~ v1_tdlat_3(X3)
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X3,sK0)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | v2_struct_0(X3) )
    | ~ spl12_68 ),
    inference(avatar_component_clause,[],[f509])).

fof(f50074,plain,
    ( ~ spl12_152
    | ~ spl12_236
    | ~ spl12_2992
    | spl12_3135 ),
    inference(avatar_contradiction_clause,[],[f50073])).

fof(f50073,plain,
    ( $false
    | ~ spl12_152
    | ~ spl12_236
    | ~ spl12_2992
    | ~ spl12_3135 ),
    inference(subsumption_resolution,[],[f46637,f49855])).

fof(f49855,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_3135 ),
    inference(avatar_component_clause,[],[f49854])).

fof(f49854,plain,
    ( spl12_3135
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK6(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3135])])).

fof(f46637,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_152
    | ~ spl12_236
    | ~ spl12_2992 ),
    inference(forward_demodulation,[],[f46636,f1956])).

fof(f1956,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl12_236 ),
    inference(avatar_component_clause,[],[f1955])).

fof(f1955,plain,
    ( spl12_236
  <=> u1_struct_0(sK1) = u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_236])])).

fof(f46636,plain,
    ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_152
    | ~ spl12_236
    | ~ spl12_2992 ),
    inference(subsumption_resolution,[],[f46624,f1956])).

fof(f46624,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_152
    | ~ spl12_2992 ),
    inference(resolution,[],[f46433,f1373])).

fof(f1373,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl12_152 ),
    inference(avatar_component_clause,[],[f1372])).

fof(f1372,plain,
    ( spl12_152
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_152])])).

fof(f46433,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | u1_struct_0(sK1) != u1_struct_0(X0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = sK6(sK0,u1_struct_0(sK1)) )
    | ~ spl12_2992 ),
    inference(avatar_component_clause,[],[f46432])).

fof(f46432,plain,
    ( spl12_2992
  <=> ! [X0] :
        ( u1_struct_0(sK1) != u1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = sK6(sK0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2992])])).

fof(f49983,plain,
    ( spl12_3152
    | ~ spl12_26
    | ~ spl12_870
    | ~ spl12_2992 ),
    inference(avatar_split_clause,[],[f49840,f46432,f6896,f273,f49981])).

fof(f273,plain,
    ( spl12_26
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_26])])).

fof(f6896,plain,
    ( spl12_870
  <=> ! [X7,X6] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_870])])).

fof(f49840,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 )
    | ~ spl12_26
    | ~ spl12_870
    | ~ spl12_2992 ),
    inference(backward_demodulation,[],[f46632,f6897])).

fof(f6897,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 )
    | ~ spl12_870 ),
    inference(avatar_component_clause,[],[f6896])).

fof(f46632,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_26
    | ~ spl12_2992 ),
    inference(trivial_inequality_removal,[],[f46623])).

fof(f46623,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_26
    | ~ spl12_2992 ),
    inference(resolution,[],[f46433,f274])).

fof(f274,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl12_26 ),
    inference(avatar_component_clause,[],[f273])).

fof(f49856,plain,
    ( ~ spl12_3135
    | ~ spl12_26
    | spl12_361
    | ~ spl12_2992 ),
    inference(avatar_split_clause,[],[f49836,f46432,f3092,f273,f49854])).

fof(f3092,plain,
    ( spl12_361
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_361])])).

fof(f49836,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2)) != sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_26
    | ~ spl12_361
    | ~ spl12_2992 ),
    inference(backward_demodulation,[],[f46632,f3093])).

fof(f3093,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl12_361 ),
    inference(avatar_component_clause,[],[f3092])).

fof(f49849,plain,
    ( spl12_3132
    | ~ spl12_26
    | ~ spl12_2992 ),
    inference(avatar_split_clause,[],[f46632,f46432,f273,f49847])).

fof(f46596,plain,
    ( spl12_2992
    | ~ spl12_4
    | ~ spl12_210
    | ~ spl12_852 ),
    inference(avatar_split_clause,[],[f45872,f6709,f1762,f196,f46432])).

fof(f1762,plain,
    ( spl12_210
  <=> m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_210])])).

fof(f6709,plain,
    ( spl12_852
  <=> ! [X3,X2] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK1) != u1_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),X3)
        | ~ l1_pre_topc(X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_852])])).

fof(f45872,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) != u1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = sK6(sK0,u1_struct_0(sK1)) )
    | ~ spl12_4
    | ~ spl12_210
    | ~ spl12_852 ),
    inference(subsumption_resolution,[],[f45870,f197])).

fof(f45870,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) != u1_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = sK6(sK0,u1_struct_0(sK1))
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_210
    | ~ spl12_852 ),
    inference(resolution,[],[f6710,f1763])).

fof(f1763,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl12_210 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f6710,plain,
    ( ! [X2,X3] :
        ( ~ m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),X3)
        | u1_struct_0(sK1) != u1_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK6(sK0,u1_struct_0(sK1))
        | ~ l1_pre_topc(X3) )
    | ~ spl12_852 ),
    inference(avatar_component_clause,[],[f6709])).

fof(f30208,plain,
    ( ~ spl12_4
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | spl12_1539 ),
    inference(avatar_contradiction_clause,[],[f30207])).

fof(f30207,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_1539 ),
    inference(subsumption_resolution,[],[f30206,f197])).

fof(f30206,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_1539 ),
    inference(subsumption_resolution,[],[f30205,f926])).

fof(f30205,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_1539 ),
    inference(subsumption_resolution,[],[f30204,f696])).

fof(f30204,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_1539 ),
    inference(subsumption_resolution,[],[f30202,f605])).

fof(f30202,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_1539 ),
    inference(resolution,[],[f19223,f133])).

fof(f19223,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl12_1539 ),
    inference(avatar_component_clause,[],[f19222])).

fof(f19222,plain,
    ( spl12_1539
  <=> ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1539])])).

fof(f30200,plain,
    ( ~ spl12_1539
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_1502
    | spl12_1509
    | ~ spl12_1850 ),
    inference(avatar_split_clause,[],[f30181,f23208,f18866,f18730,f196,f189,f182,f19222])).

fof(f18730,plain,
    ( spl12_1502
  <=> m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1502])])).

fof(f23208,plain,
    ( spl12_1850
  <=> v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1850])])).

fof(f30181,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_1502
    | ~ spl12_1509
    | ~ spl12_1850 ),
    inference(subsumption_resolution,[],[f30180,f183])).

fof(f30180,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_1502
    | ~ spl12_1509
    | ~ spl12_1850 ),
    inference(subsumption_resolution,[],[f30179,f190])).

fof(f30179,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_1502
    | ~ spl12_1509
    | ~ spl12_1850 ),
    inference(subsumption_resolution,[],[f30178,f197])).

fof(f30178,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1502
    | ~ spl12_1509
    | ~ spl12_1850 ),
    inference(subsumption_resolution,[],[f30177,f18867])).

fof(f30177,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1502
    | ~ spl12_1850 ),
    inference(subsumption_resolution,[],[f30168,f18731])).

fof(f18731,plain,
    ( m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_1502 ),
    inference(avatar_component_clause,[],[f18730])).

fof(f30168,plain,
    ( ~ v2_tex_2(sK4(sK0,u1_struct_0(sK1)),sK0)
    | ~ m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_1850 ),
    inference(resolution,[],[f23209,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK6(X0,X1))
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f23209,plain,
    ( v2_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1850 ),
    inference(avatar_component_clause,[],[f23208])).

fof(f26824,plain,
    ( ~ spl12_2
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_1510
    | ~ spl12_1572
    | ~ spl12_2012
    | spl12_2037 ),
    inference(avatar_contradiction_clause,[],[f26823])).

fof(f26823,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_1510
    | ~ spl12_1572
    | ~ spl12_2012
    | ~ spl12_2037 ),
    inference(unit_resulting_resolution,[],[f190,f197,f274,f19699,f18876,f26815,f26579])).

fof(f26579,plain,
    ( ! [X8,X9] :
        ( ~ m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),X9)
        | m1_pre_topc(X8,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
        | ~ r1_tarski(u1_struct_0(X8),sK4(sK0,u1_struct_0(sK1)))
        | ~ m1_pre_topc(X8,X9)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl12_2012 ),
    inference(avatar_component_clause,[],[f26578])).

fof(f26578,plain,
    ( spl12_2012
  <=> ! [X9,X8] :
        ( ~ r1_tarski(u1_struct_0(X8),sK4(sK0,u1_struct_0(sK1)))
        | m1_pre_topc(X8,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),X9)
        | ~ m1_pre_topc(X8,X9)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2012])])).

fof(f26815,plain,
    ( ~ m1_pre_topc(sK1,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_2037 ),
    inference(avatar_component_clause,[],[f26814])).

fof(f19699,plain,
    ( r1_tarski(u1_struct_0(sK1),sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_1572 ),
    inference(avatar_component_clause,[],[f19698])).

fof(f19698,plain,
    ( spl12_1572
  <=> r1_tarski(u1_struct_0(sK1),sK4(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1572])])).

fof(f26598,plain,
    ( spl12_2012
    | ~ spl12_1524 ),
    inference(avatar_split_clause,[],[f25762,f19043,f26578])).

fof(f25762,plain,
    ( ! [X8,X9] :
        ( ~ r1_tarski(u1_struct_0(X8),sK4(sK0,u1_struct_0(sK1)))
        | m1_pre_topc(X8,sK6(sK0,sK4(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),X9)
        | ~ m1_pre_topc(X8,X9)
        | ~ l1_pre_topc(X9)
        | ~ v2_pre_topc(X9) )
    | ~ spl12_1524 ),
    inference(superposition,[],[f149,f19044])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f97,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t4_tsep_1)).

fof(f22481,plain,
    ( spl12_189
    | ~ spl12_1498
    | ~ spl12_1508 ),
    inference(avatar_contradiction_clause,[],[f22474])).

fof(f22474,plain,
    ( $false
    | ~ spl12_189
    | ~ spl12_1498
    | ~ spl12_1508 ),
    inference(unit_resulting_resolution,[],[f1648,f18704,f18870,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',cc1_subset_1)).

fof(f18870,plain,
    ( v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_1508 ),
    inference(avatar_component_clause,[],[f18869])).

fof(f18869,plain,
    ( spl12_1508
  <=> v1_xboole_0(sK4(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1508])])).

fof(f18704,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_1498 ),
    inference(avatar_component_clause,[],[f18703])).

fof(f18703,plain,
    ( spl12_1498
  <=> m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_1498])])).

fof(f1648,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_189 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f1647,plain,
    ( spl12_189
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_189])])).

fof(f20725,plain,
    ( ~ spl12_4
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_1640 ),
    inference(avatar_contradiction_clause,[],[f20724])).

fof(f20724,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_1640 ),
    inference(subsumption_resolution,[],[f20723,f197])).

fof(f20723,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_1640 ),
    inference(subsumption_resolution,[],[f20722,f926])).

fof(f20722,plain,
    ( ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_1640 ),
    inference(subsumption_resolution,[],[f20721,f696])).

fof(f20721,plain,
    ( ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_79
    | ~ spl12_1640 ),
    inference(subsumption_resolution,[],[f20686,f605])).

fof(f20686,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_1640 ),
    inference(trivial_inequality_removal,[],[f20676])).

fof(f20676,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK1)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_1640 ),
    inference(superposition,[],[f135,f20387])).

fof(f20387,plain,
    ( u1_struct_0(sK1) = sK4(sK0,u1_struct_0(sK1))
    | ~ spl12_1640 ),
    inference(avatar_component_clause,[],[f20386])).

fof(f135,plain,(
    ! [X0,X1] :
      ( sK4(X0,X1) != X1
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f19700,plain,
    ( spl12_1572
    | ~ spl12_1498 ),
    inference(avatar_split_clause,[],[f18711,f18703,f19698])).

fof(f18711,plain,
    ( r1_tarski(u1_struct_0(sK1),sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_1498 ),
    inference(resolution,[],[f18704,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t3_subset)).

fof(f19045,plain,
    ( spl12_1508
    | spl12_1524
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_140 ),
    inference(avatar_split_clause,[],[f19030,f1121,f925,f695,f604,f19043,f18869])).

fof(f1121,plain,
    ( spl12_140
  <=> ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | u1_struct_0(sK6(sK0,sK4(sK0,X0))) = sK4(sK0,X0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_140])])).

fof(f19030,plain,
    ( u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) = sK4(sK0,u1_struct_0(sK1))
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f17586,f605])).

fof(f17586,plain,
    ( u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) = sK4(sK0,u1_struct_0(sK1))
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_140 ),
    inference(subsumption_resolution,[],[f8794,f926])).

fof(f8794,plain,
    ( u1_struct_0(sK6(sK0,sK4(sK0,u1_struct_0(sK1)))) = sK4(sK0,u1_struct_0(sK1))
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_84
    | ~ spl12_140 ),
    inference(resolution,[],[f1122,f696])).

fof(f1122,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | u1_struct_0(sK6(sK0,sK4(sK0,X0))) = sK4(sK0,X0)
        | v3_tex_2(X0,sK0)
        | v1_xboole_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_140 ),
    inference(avatar_component_clause,[],[f1121])).

fof(f18877,plain,
    ( spl12_1508
    | spl12_1510
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_134 ),
    inference(avatar_split_clause,[],[f18863,f1098,f925,f695,f604,f18875,f18869])).

fof(f1098,plain,
    ( spl12_134
  <=> ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | m1_pre_topc(sK6(sK0,sK4(sK0,X0)),sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_134])])).

fof(f18863,plain,
    ( m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_134 ),
    inference(subsumption_resolution,[],[f17587,f605])).

fof(f17587,plain,
    ( m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_134 ),
    inference(subsumption_resolution,[],[f8769,f926])).

fof(f8769,plain,
    ( m1_pre_topc(sK6(sK0,sK4(sK0,u1_struct_0(sK1))),sK0)
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | v1_xboole_0(sK4(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_84
    | ~ spl12_134 ),
    inference(resolution,[],[f1099,f696])).

fof(f1099,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | m1_pre_topc(sK6(sK0,sK4(sK0,X0)),sK0)
        | v3_tex_2(X0,sK0)
        | v1_xboole_0(sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_134 ),
    inference(avatar_component_clause,[],[f1098])).

fof(f18732,plain,
    ( spl12_1502
    | ~ spl12_4
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f18718,f925,f695,f604,f196,f18730])).

fof(f18718,plain,
    ( m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f17602,f605])).

fof(f17602,plain,
    ( m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f17601,f197])).

fof(f17601,plain,
    ( m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1341,f926])).

fof(f1341,plain,
    ( m1_subset_1(sK4(sK0,u1_struct_0(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_84 ),
    inference(resolution,[],[f696,f132])).

fof(f18705,plain,
    ( spl12_1498
    | ~ spl12_4
    | spl12_79
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f18697,f925,f695,f604,f196,f18703])).

fof(f18697,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_4
    | ~ spl12_79
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f17600,f605])).

fof(f17600,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f17599,f197])).

fof(f17599,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1346,f926])).

fof(f1346,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(sK4(sK0,u1_struct_0(sK1))))
    | ~ spl12_84 ),
    inference(resolution,[],[f696,f406])).

fof(f406,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X0,X1)
      | v3_tex_2(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | m1_subset_1(X0,k1_zfmisc_1(sK4(X1,X0))) ) ),
    inference(resolution,[],[f134,f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f134,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,sK4(X0,X1))
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f9297,plain,
    ( ~ spl12_4
    | ~ spl12_152
    | spl12_973 ),
    inference(avatar_contradiction_clause,[],[f9296])).

fof(f9296,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_152
    | ~ spl12_973 ),
    inference(subsumption_resolution,[],[f9295,f197])).

fof(f9295,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl12_152
    | ~ spl12_973 ),
    inference(subsumption_resolution,[],[f9288,f1373])).

fof(f9288,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_973 ),
    inference(resolution,[],[f9282,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t1_tsep_1)).

fof(f9282,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_973 ),
    inference(avatar_component_clause,[],[f9281])).

fof(f9281,plain,
    ( spl12_973
  <=> ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_973])])).

fof(f9283,plain,
    ( ~ spl12_973
    | ~ spl12_168
    | ~ spl12_174
    | ~ spl12_176
    | spl12_237 ),
    inference(avatar_split_clause,[],[f9275,f1952,f1542,f1533,f1481,f9281])).

fof(f1481,plain,
    ( spl12_168
  <=> v2_tex_2(u1_struct_0(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_168])])).

fof(f1533,plain,
    ( spl12_174
  <=> ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_174])])).

fof(f1542,plain,
    ( spl12_176
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_176])])).

fof(f1952,plain,
    ( spl12_237
  <=> u1_struct_0(sK1) != u1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_237])])).

fof(f9275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_168
    | ~ spl12_174
    | ~ spl12_176
    | ~ spl12_237 ),
    inference(subsumption_resolution,[],[f2590,f1953])).

fof(f1953,plain,
    ( u1_struct_0(sK1) != u1_struct_0(sK2)
    | ~ spl12_237 ),
    inference(avatar_component_clause,[],[f1952])).

fof(f2590,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl12_168
    | ~ spl12_174
    | ~ spl12_176 ),
    inference(subsumption_resolution,[],[f1612,f1543])).

fof(f1543,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl12_176 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f1612,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(u1_struct_0(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK1) = u1_struct_0(sK2)
    | ~ spl12_168
    | ~ spl12_174 ),
    inference(resolution,[],[f1534,f1482])).

fof(f1482,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ spl12_168 ),
    inference(avatar_component_clause,[],[f1481])).

fof(f1534,plain,
    ( ! [X0] :
        ( ~ v2_tex_2(X0,sK0)
        | ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK1) = X0 )
    | ~ spl12_174 ),
    inference(avatar_component_clause,[],[f1533])).

fof(f6898,plain,
    ( spl12_870
    | ~ spl12_340
    | ~ spl12_862 ),
    inference(avatar_split_clause,[],[f6893,f6826,f2857,f6896])).

fof(f2857,plain,
    ( spl12_340
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_340])])).

fof(f6826,plain,
    ( spl12_862
  <=> m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_862])])).

fof(f6893,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6 )
    | ~ spl12_340
    | ~ spl12_862 ),
    inference(subsumption_resolution,[],[f2893,f6827])).

fof(f6827,plain,
    ( m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl12_862 ),
    inference(avatar_component_clause,[],[f6826])).

fof(f2893,plain,
    ( ! [X6,X7] :
        ( g1_pre_topc(X6,X7) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))
        | u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) = X6
        | ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) )
    | ~ spl12_340 ),
    inference(superposition,[],[f157,f2858])).

fof(f2858,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl12_340 ),
    inference(avatar_component_clause,[],[f2857])).

fof(f157,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',free_g1_pre_topc)).

fof(f6844,plain,
    ( ~ spl12_530
    | spl12_863 ),
    inference(avatar_contradiction_clause,[],[f6843])).

fof(f6843,plain,
    ( $false
    | ~ spl12_530
    | ~ spl12_863 ),
    inference(subsumption_resolution,[],[f6840,f4094])).

fof(f4094,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl12_530 ),
    inference(avatar_component_clause,[],[f4093])).

fof(f4093,plain,
    ( spl12_530
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_530])])).

fof(f6840,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl12_863 ),
    inference(resolution,[],[f6830,f125])).

fof(f125,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',dt_u1_pre_topc)).

fof(f6830,plain,
    ( ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl12_863 ),
    inference(avatar_component_clause,[],[f6829])).

fof(f6829,plain,
    ( spl12_863
  <=> ~ m1_subset_1(u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_863])])).

fof(f6711,plain,
    ( spl12_852
    | ~ spl12_278
    | ~ spl12_736 ),
    inference(avatar_split_clause,[],[f6705,f5701,f2217,f6709])).

fof(f5701,plain,
    ( spl12_736
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK6(sK0,u1_struct_0(sK1)))) = sK6(sK0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_736])])).

fof(f6705,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = sK6(sK0,u1_struct_0(sK1))
        | u1_struct_0(sK1) != u1_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl12_278
    | ~ spl12_736 ),
    inference(forward_demodulation,[],[f2244,f5702])).

fof(f5702,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK6(sK0,u1_struct_0(sK1)))) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_736 ),
    inference(avatar_component_clause,[],[f5701])).

fof(f2244,plain,
    ( ! [X2,X3] :
        ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK6(sK0,u1_struct_0(sK1))))
        | u1_struct_0(sK1) != u1_struct_0(X2)
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl12_278 ),
    inference(forward_demodulation,[],[f2224,f2218])).

fof(f2224,plain,
    ( ! [X2,X3] :
        ( u1_struct_0(sK1) != u1_struct_0(X2)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = g1_pre_topc(u1_struct_0(sK6(sK0,u1_struct_0(sK1))),u1_pre_topc(sK6(sK0,u1_struct_0(sK1))))
        | ~ m1_pre_topc(X2,X3)
        | ~ m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),X3)
        | ~ l1_pre_topc(X3) )
    | ~ spl12_278 ),
    inference(superposition,[],[f129,f2218])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( u1_struct_0(X1) != u1_struct_0(X2)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              | u1_struct_0(X1) != u1_struct_0(X2)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( u1_struct_0(X1) = u1_struct_0(X2)
               => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t5_tsep_1)).

fof(f5703,plain,
    ( spl12_736
    | ~ spl12_190
    | ~ spl12_234
    | ~ spl12_278 ),
    inference(avatar_split_clause,[],[f5693,f2217,f1948,f1656,f5701])).

fof(f1656,plain,
    ( spl12_190
  <=> v1_pre_topc(sK6(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_190])])).

fof(f1948,plain,
    ( spl12_234
  <=> l1_pre_topc(sK6(sK0,u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_234])])).

fof(f5693,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK6(sK0,u1_struct_0(sK1)))) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_190
    | ~ spl12_234
    | ~ spl12_278 ),
    inference(forward_demodulation,[],[f5692,f2218])).

fof(f5692,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK0,u1_struct_0(sK1))),u1_pre_topc(sK6(sK0,u1_struct_0(sK1)))) = sK6(sK0,u1_struct_0(sK1))
    | ~ spl12_190
    | ~ spl12_234 ),
    inference(subsumption_resolution,[],[f1678,f1949])).

fof(f1949,plain,
    ( l1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_234 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f1678,plain,
    ( g1_pre_topc(u1_struct_0(sK6(sK0,u1_struct_0(sK1))),u1_pre_topc(sK6(sK0,u1_struct_0(sK1)))) = sK6(sK0,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_190 ),
    inference(resolution,[],[f1657,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',abstractness_v1_pre_topc)).

fof(f1657,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_190 ),
    inference(avatar_component_clause,[],[f1656])).

fof(f4116,plain,
    ( ~ spl12_38
    | spl12_531 ),
    inference(avatar_contradiction_clause,[],[f4115])).

fof(f4115,plain,
    ( $false
    | ~ spl12_38
    | ~ spl12_531 ),
    inference(subsumption_resolution,[],[f4113,f322])).

fof(f322,plain,
    ( l1_pre_topc(sK1)
    | ~ spl12_38 ),
    inference(avatar_component_clause,[],[f321])).

fof(f321,plain,
    ( spl12_38
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_38])])).

fof(f4113,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl12_531 ),
    inference(resolution,[],[f4097,f359])).

fof(f359,plain,(
    ! [X2] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f156,f125])).

fof(f156,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',dt_g1_pre_topc)).

fof(f4097,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl12_531 ),
    inference(avatar_component_clause,[],[f4096])).

fof(f4096,plain,
    ( spl12_531
  <=> ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_531])])).

fof(f3094,plain,
    ( ~ spl12_361
    | spl12_157
    | ~ spl12_236 ),
    inference(avatar_split_clause,[],[f2984,f1955,f1396,f3092])).

fof(f1396,plain,
    ( spl12_157
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_157])])).

fof(f2984,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK2))
    | ~ spl12_157
    | ~ spl12_236 ),
    inference(backward_demodulation,[],[f1956,f1397])).

fof(f1397,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl12_157 ),
    inference(avatar_component_clause,[],[f1396])).

fof(f2859,plain,
    ( spl12_340
    | ~ spl12_38 ),
    inference(avatar_split_clause,[],[f1170,f321,f2857])).

fof(f1170,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl12_38 ),
    inference(resolution,[],[f1165,f322])).

fof(f1165,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) ) ),
    inference(subsumption_resolution,[],[f561,f359])).

fof(f561,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f348,f126])).

fof(f348,plain,(
    ! [X2] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f155,f125])).

fof(f155,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | v1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f2437,plain,
    ( ~ spl12_26
    | ~ spl12_86
    | ~ spl12_150
    | ~ spl12_152
    | spl12_177 ),
    inference(avatar_contradiction_clause,[],[f2436])).

fof(f2436,plain,
    ( $false
    | ~ spl12_26
    | ~ spl12_86
    | ~ spl12_150
    | ~ spl12_152
    | ~ spl12_177 ),
    inference(subsumption_resolution,[],[f2435,f1313])).

fof(f1313,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl12_150 ),
    inference(avatar_component_clause,[],[f1312])).

fof(f1312,plain,
    ( spl12_150
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_150])])).

fof(f2435,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ spl12_26
    | ~ spl12_86
    | ~ spl12_152
    | ~ spl12_177 ),
    inference(subsumption_resolution,[],[f2434,f274])).

fof(f2434,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ spl12_86
    | ~ spl12_152
    | ~ spl12_177 ),
    inference(subsumption_resolution,[],[f2429,f1373])).

fof(f2429,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ spl12_86
    | ~ spl12_177 ),
    inference(resolution,[],[f1540,f719])).

fof(f719,plain,
    ( ! [X0,X1] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X1) )
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f718])).

fof(f718,plain,
    ( spl12_86
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f1540,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl12_177 ),
    inference(avatar_component_clause,[],[f1539])).

fof(f1539,plain,
    ( spl12_177
  <=> ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_177])])).

fof(f2219,plain,
    ( spl12_278
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114
    | spl12_189 ),
    inference(avatar_split_clause,[],[f2035,f1647,f925,f695,f196,f189,f182,f2217])).

fof(f2035,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_189 ),
    inference(subsumption_resolution,[],[f1365,f1648])).

fof(f1365,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1364,f183])).

fof(f1364,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1363,f190])).

fof(f1363,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1362,f197])).

fof(f1362,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1345,f926])).

fof(f1345,plain,
    ( u1_struct_0(sK1) = u1_struct_0(sK6(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84 ),
    inference(resolution,[],[f696,f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK6(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f1950,plain,
    ( spl12_234
    | ~ spl12_4
    | ~ spl12_210 ),
    inference(avatar_split_clause,[],[f1771,f1762,f196,f1948])).

fof(f1771,plain,
    ( l1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ spl12_4
    | ~ spl12_210 ),
    inference(subsumption_resolution,[],[f1768,f197])).

fof(f1768,plain,
    ( l1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_210 ),
    inference(resolution,[],[f1763,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',dt_m1_pre_topc)).

fof(f1764,plain,
    ( spl12_210
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114
    | spl12_189 ),
    inference(avatar_split_clause,[],[f1753,f1647,f925,f695,f196,f189,f182,f1762])).

fof(f1753,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114
    | ~ spl12_189 ),
    inference(subsumption_resolution,[],[f1361,f1648])).

fof(f1361,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1360,f183])).

fof(f1360,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1359,f190])).

fof(f1359,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1358,f197])).

fof(f1358,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1344,f926])).

fof(f1344,plain,
    ( m1_pre_topc(sK6(sK0,u1_struct_0(sK1)),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84 ),
    inference(resolution,[],[f696,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK6(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f1677,plain,
    ( ~ spl12_38
    | spl12_193 ),
    inference(avatar_contradiction_clause,[],[f1676])).

fof(f1676,plain,
    ( $false
    | ~ spl12_38
    | ~ spl12_193 ),
    inference(subsumption_resolution,[],[f1674,f322])).

fof(f1674,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl12_193 ),
    inference(resolution,[],[f1670,f124])).

fof(f124,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',dt_l1_pre_topc)).

fof(f1670,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl12_193 ),
    inference(avatar_component_clause,[],[f1669])).

fof(f1669,plain,
    ( spl12_193
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_193])])).

fof(f1671,plain,
    ( ~ spl12_193
    | spl12_7
    | ~ spl12_188 ),
    inference(avatar_split_clause,[],[f1664,f1650,f203,f1669])).

fof(f203,plain,
    ( spl12_7
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_7])])).

fof(f1650,plain,
    ( spl12_188
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_188])])).

fof(f1664,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl12_7
    | ~ spl12_188 ),
    inference(subsumption_resolution,[],[f1659,f204])).

fof(f204,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl12_7 ),
    inference(avatar_component_clause,[],[f203])).

fof(f1659,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl12_188 ),
    inference(resolution,[],[f1651,f139])).

fof(f139,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',fc2_struct_0)).

fof(f1651,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_188 ),
    inference(avatar_component_clause,[],[f1650])).

fof(f1658,plain,
    ( spl12_188
    | spl12_190
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f1353,f925,f695,f196,f189,f182,f1656,f1650])).

fof(f1353,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1352,f183])).

fof(f1352,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | v2_struct_0(sK0)
    | ~ spl12_2
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1351,f190])).

fof(f1351,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1350,f197])).

fof(f1350,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1342,f926])).

fof(f1342,plain,
    ( v1_pre_topc(sK6(sK0,u1_struct_0(sK1)))
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_84 ),
    inference(resolution,[],[f696,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | v1_pre_topc(sK6(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f1535,plain,
    ( spl12_174
    | ~ spl12_4
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f1306,f925,f607,f196,f1533])).

fof(f607,plain,
    ( spl12_78
  <=> v3_tex_2(u1_struct_0(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_78])])).

fof(f1306,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK1) = X0 )
    | ~ spl12_4
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1305,f197])).

fof(f1305,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK1) = X0
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1303,f926])).

fof(f1303,plain,
    ( ! [X0] :
        ( ~ r1_tarski(u1_struct_0(sK1),X0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK1) = X0
        | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl12_78 ),
    inference(resolution,[],[f608,f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ r1_tarski(X1,X3)
      | ~ v2_tex_2(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f608,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_78 ),
    inference(avatar_component_clause,[],[f607])).

fof(f1483,plain,
    ( spl12_168
    | spl12_1
    | ~ spl12_4
    | ~ spl12_152
    | ~ spl12_164 ),
    inference(avatar_split_clause,[],[f1476,f1441,f1372,f196,f182,f1481])).

fof(f1441,plain,
    ( spl12_164
  <=> ! [X0] :
        ( v2_tex_2(u1_struct_0(sK2),X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_164])])).

fof(f1476,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_152
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f1475,f183])).

fof(f1475,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_152
    | ~ spl12_164 ),
    inference(subsumption_resolution,[],[f1474,f197])).

fof(f1474,plain,
    ( v2_tex_2(u1_struct_0(sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_152
    | ~ spl12_164 ),
    inference(resolution,[],[f1442,f1373])).

fof(f1442,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | v2_tex_2(u1_struct_0(sK2),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_164 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1443,plain,
    ( spl12_164
    | spl12_37
    | ~ spl12_70 ),
    inference(avatar_split_clause,[],[f1297,f525,f310,f1441])).

fof(f310,plain,
    ( spl12_37
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_37])])).

fof(f525,plain,
    ( spl12_70
  <=> v1_tdlat_3(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_70])])).

fof(f1297,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK2),X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_37
    | ~ spl12_70 ),
    inference(subsumption_resolution,[],[f1296,f311])).

fof(f311,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl12_37 ),
    inference(avatar_component_clause,[],[f310])).

fof(f1296,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK2),X0)
        | ~ m1_pre_topc(sK2,X0)
        | v2_struct_0(sK2)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_70 ),
    inference(resolution,[],[f526,f457])).

fof(f457,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f174,f128])).

fof(f174,plain,(
    ! [X0,X1] :
      ( v2_tex_2(u1_struct_0(X1),X0)
      | ~ v1_tdlat_3(X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( v2_tex_2(X2,X0)
      | ~ v1_tdlat_3(X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_tex_2(X2,X0)
                  | ~ v1_tdlat_3(X1) )
                & ( v1_tdlat_3(X1)
                  | ~ v2_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t26_tex_2)).

fof(f526,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl12_70 ),
    inference(avatar_component_clause,[],[f525])).

fof(f1398,plain,
    ( ~ spl12_157
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f1390,f286,f280,f1396])).

fof(f280,plain,
    ( spl12_28
  <=> v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_28])])).

fof(f286,plain,
    ( spl12_30
  <=> v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_30])])).

fof(f1390,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1389,f281])).

fof(f281,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl12_28 ),
    inference(avatar_component_clause,[],[f280])).

fof(f1389,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f118,f287])).

fof(f287,plain,
    ( v1_tdlat_3(sK1)
    | ~ spl12_30 ),
    inference(avatar_component_clause,[],[f286])).

fof(f118,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,
    ( ( ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(sK2,sK0)
        & v1_tdlat_3(sK2)
        & ~ v2_struct_0(sK2) )
      | ~ v1_tdlat_3(sK1)
      | ~ v4_tex_2(sK1,sK0) )
    & ( ( ! [X3] :
            ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
            | ~ m1_pre_topc(sK1,X3)
            | ~ m1_pre_topc(X3,sK0)
            | ~ v1_tdlat_3(X3)
            | v2_struct_0(X3) )
        & v1_tdlat_3(sK1) )
      | v4_tex_2(sK1,sK0) )
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f79,f82,f81,f80])).

fof(f80,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ? [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X2,X0)
                  & v1_tdlat_3(X2)
                  & ~ v2_struct_0(X2) )
              | ~ v1_tdlat_3(X1)
              | ~ v4_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                    | ~ m1_pre_topc(X1,X3)
                    | ~ m1_pre_topc(X3,X0)
                    | ~ v1_tdlat_3(X3)
                    | v2_struct_0(X3) )
                & v1_tdlat_3(X1) )
              | v4_tex_2(X1,X0) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,sK0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,sK0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,sK0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,sK0) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f81,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
     => ( ( ? [X2] :
              ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
              & m1_pre_topc(sK1,X2)
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & ~ v2_struct_0(X2) )
          | ~ v1_tdlat_3(sK1)
          | ~ v4_tex_2(sK1,X0) )
        & ( ( ! [X3] :
                ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                | ~ m1_pre_topc(sK1,X3)
                | ~ m1_pre_topc(X3,X0)
                | ~ v1_tdlat_3(X3)
                | v2_struct_0(X3) )
            & v1_tdlat_3(sK1) )
          | v4_tex_2(sK1,X0) )
        & m1_pre_topc(sK1,X0)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
          & m1_pre_topc(X1,X2)
          & m1_pre_topc(X2,X0)
          & v1_tdlat_3(X2)
          & ~ v2_struct_0(X2) )
     => ( g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
        & m1_pre_topc(X1,sK2)
        & m1_pre_topc(sK2,X0)
        & v1_tdlat_3(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X3] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
                  | ~ m1_pre_topc(X1,X3)
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_tdlat_3(X3)
                  | v2_struct_0(X3) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f77])).

fof(f77,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ? [X2] :
                ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X2,X0)
                & v1_tdlat_3(X2)
                & ~ v2_struct_0(X2) )
            | ~ v1_tdlat_3(X1)
            | ~ v4_tex_2(X1,X0) )
          & ( ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) )
            | v4_tex_2(X1,X0) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_tex_2(X1,X0)
          <~> ( ! [X2] :
                  ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tdlat_3(X2)
                  | v2_struct_0(X2) )
              & v1_tdlat_3(X1) ) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( v4_tex_2(X1,X0)
            <=> ( ! [X2] :
                    ( ( m1_pre_topc(X2,X0)
                      & v1_tdlat_3(X2)
                      & ~ v2_struct_0(X2) )
                   => ( m1_pre_topc(X1,X2)
                     => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
                & v1_tdlat_3(X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( v4_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & ~ v2_struct_0(X2) )
                 => ( m1_pre_topc(X1,X2)
                   => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) )
              & v1_tdlat_3(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t52_tex_2)).

fof(f1374,plain,
    ( spl12_152
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f1367,f286,f280,f1372])).

fof(f1367,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1366,f281])).

fof(f1366,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f116,f287])).

fof(f116,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f1336,plain,
    ( spl12_28
    | spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_78 ),
    inference(avatar_split_clause,[],[f1329,f607,f273,f196,f182,f280])).

fof(f1329,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_78 ),
    inference(subsumption_resolution,[],[f1328,f183])).

fof(f1328,plain,
    ( v4_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_78 ),
    inference(subsumption_resolution,[],[f1327,f197])).

fof(f1327,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_26
    | ~ spl12_78 ),
    inference(subsumption_resolution,[],[f1302,f274])).

fof(f1302,plain,
    ( v4_tex_2(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_78 ),
    inference(resolution,[],[f608,f450])).

fof(f450,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(u1_struct_0(X1),X0)
      | v4_tex_2(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f173,f128])).

fof(f173,plain,(
    ! [X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( v4_tex_2(X1,X0)
      | ~ v3_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v3_tex_2(X2,X0)
                  | ~ v4_tex_2(X1,X0) )
                & ( v4_tex_2(X1,X0)
                  | ~ v3_tex_2(X2,X0) ) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tex_2(X2,X0)
              <=> v4_tex_2(X1,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v3_tex_2(X2,X0)
                <=> v4_tex_2(X1,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tex_2__t52_tex_2.p',t51_tex_2)).

fof(f1326,plain,
    ( spl12_84
    | ~ spl12_4
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(avatar_split_clause,[],[f1325,f925,f607,f196,f695])).

fof(f1325,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_4
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1324,f197])).

fof(f1324,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_78
    | ~ spl12_114 ),
    inference(subsumption_resolution,[],[f1304,f926])).

fof(f1304,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl12_78 ),
    inference(resolution,[],[f608,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f1323,plain,
    ( spl12_1
    | ~ spl12_4
    | spl12_7
    | ~ spl12_26
    | spl12_31
    | ~ spl12_84 ),
    inference(avatar_contradiction_clause,[],[f1322])).

fof(f1322,plain,
    ( $false
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_7
    | ~ spl12_26
    | ~ spl12_31
    | ~ spl12_84 ),
    inference(unit_resulting_resolution,[],[f183,f197,f204,f274,f696,f284,f471])).

fof(f471,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(u1_struct_0(X1),X0)
      | v1_tdlat_3(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f175,f128])).

fof(f175,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f284,plain,
    ( ~ v1_tdlat_3(sK1)
    | ~ spl12_31 ),
    inference(avatar_component_clause,[],[f283])).

fof(f283,plain,
    ( spl12_31
  <=> ~ v1_tdlat_3(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_31])])).

fof(f1314,plain,
    ( spl12_150
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f1307,f286,f280,f1312])).

fof(f1307,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f1293,f281])).

fof(f1293,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f117,f287])).

fof(f117,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f1123,plain,
    ( spl12_140
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f804,f196,f189,f182,f1121])).

fof(f804,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | u1_struct_0(sK6(sK0,sK4(sK0,X0))) = sK4(sK0,X0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f803,f183])).

fof(f803,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | u1_struct_0(sK6(sK0,sK4(sK0,X0))) = sK4(sK0,X0)
        | v2_struct_0(sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f801,f197])).

fof(f801,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | ~ l1_pre_topc(sK0)
        | u1_struct_0(sK6(sK0,sK4(sK0,X0))) = sK4(sK0,X0)
        | v2_struct_0(sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_2 ),
    inference(resolution,[],[f488,f190])).

fof(f488,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(sK6(X0,sK4(X0,X1))) = sK4(X0,X1)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f487,f132])).

fof(f487,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK6(X0,sK4(X0,X1))) = sK4(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f486])).

fof(f486,plain,(
    ! [X0,X1] :
      ( u1_struct_0(sK6(X0,sK4(X0,X1))) = sK4(X0,X1)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f144,f133])).

fof(f1100,plain,
    ( spl12_134
    | spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f781,f196,f189,f182,f1098])).

fof(f781,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | m1_pre_topc(sK6(sK0,sK4(sK0,X0)),sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_1
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f780,f183])).

fof(f780,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | m1_pre_topc(sK6(sK0,sK4(sK0,X0)),sK0)
        | v2_struct_0(sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f778,f197])).

fof(f778,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(sK0,X0))
        | ~ l1_pre_topc(sK0)
        | m1_pre_topc(sK6(sK0,sK4(sK0,X0)),sK0)
        | v2_struct_0(sK0)
        | v3_tex_2(X0,sK0)
        | ~ v2_tex_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl12_2 ),
    inference(resolution,[],[f456,f190])).

fof(f456,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(sK6(X0,sK4(X0,X1)),X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f455,f132])).

fof(f455,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK6(X0,sK4(X0,X1)),X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(sK6(X0,sK4(X0,X1)),X0)
      | ~ m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(sK4(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f143,f133])).

fof(f940,plain,
    ( ~ spl12_4
    | ~ spl12_26
    | spl12_107 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_107 ),
    inference(subsumption_resolution,[],[f938,f274])).

fof(f938,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl12_4
    | ~ spl12_107 ),
    inference(subsumption_resolution,[],[f934,f197])).

fof(f934,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl12_107 ),
    inference(resolution,[],[f880,f380])).

fof(f380,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f128,f159])).

fof(f880,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl12_107 ),
    inference(avatar_component_clause,[],[f879])).

fof(f879,plain,
    ( spl12_107
  <=> ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_107])])).

fof(f927,plain,
    ( spl12_114
    | ~ spl12_106 ),
    inference(avatar_split_clause,[],[f898,f882,f925])).

fof(f882,plain,
    ( spl12_106
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_106])])).

fof(f898,plain,
    ( m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_106 ),
    inference(resolution,[],[f883,f160])).

fof(f883,plain,
    ( r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ spl12_106 ),
    inference(avatar_component_clause,[],[f882])).

fof(f720,plain,
    ( spl12_86
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(avatar_split_clause,[],[f422,f196,f189,f718])).

fof(f422,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl12_2
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f420,f197])).

fof(f420,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f150,f190])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f697,plain,
    ( spl12_84
    | spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_76 ),
    inference(avatar_split_clause,[],[f690,f596,f273,f196,f182,f695])).

fof(f596,plain,
    ( spl12_76
  <=> ! [X0] :
        ( v2_tex_2(u1_struct_0(sK1),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_76])])).

fof(f690,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_76 ),
    inference(subsumption_resolution,[],[f689,f183])).

fof(f689,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_76 ),
    inference(subsumption_resolution,[],[f688,f197])).

fof(f688,plain,
    ( v2_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_26
    | ~ spl12_76 ),
    inference(resolution,[],[f597,f274])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | v2_tex_2(u1_struct_0(sK1),X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_76 ),
    inference(avatar_component_clause,[],[f596])).

fof(f609,plain,
    ( spl12_78
    | spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(avatar_split_clause,[],[f602,f280,f273,f196,f182,f607])).

fof(f602,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ spl12_1
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f601,f183])).

fof(f601,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | v2_struct_0(sK0)
    | ~ spl12_4
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f600,f197])).

fof(f600,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_26
    | ~ spl12_28 ),
    inference(subsumption_resolution,[],[f599,f274])).

fof(f599,plain,
    ( v3_tex_2(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl12_28 ),
    inference(resolution,[],[f281,f443])).

fof(f443,plain,(
    ! [X0,X1] :
      ( ~ v4_tex_2(X1,X0)
      | v3_tex_2(u1_struct_0(X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f172,f128])).

fof(f172,plain,(
    ! [X0,X1] :
      ( v3_tex_2(u1_struct_0(X1),X0)
      | ~ v4_tex_2(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( v3_tex_2(X2,X0)
      | ~ v4_tex_2(X1,X0)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f598,plain,
    ( spl12_76
    | spl12_7
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f466,f286,f203,f596])).

fof(f466,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK1),X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_7
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f465,f204])).

fof(f465,plain,
    ( ! [X0] :
        ( v2_tex_2(u1_struct_0(sK1),X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl12_30 ),
    inference(resolution,[],[f457,f287])).

fof(f527,plain,
    ( spl12_70
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f520,f286,f280,f525])).

fof(f520,plain,
    ( v1_tdlat_3(sK2)
    | ~ spl12_28
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f515,f281])).

fof(f515,plain,
    ( v1_tdlat_3(sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f115,f287])).

fof(f115,plain,
    ( v1_tdlat_3(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f511,plain,
    ( spl12_68
    | spl12_29 ),
    inference(avatar_split_clause,[],[f493,f277,f509])).

fof(f277,plain,
    ( spl12_29
  <=> ~ v4_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_29])])).

fof(f493,plain,
    ( ! [X3] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
        | ~ m1_pre_topc(sK1,X3)
        | ~ m1_pre_topc(X3,sK0)
        | ~ v1_tdlat_3(X3)
        | v2_struct_0(X3) )
    | ~ spl12_29 ),
    inference(subsumption_resolution,[],[f113,f278])).

fof(f278,plain,
    ( ~ v4_tex_2(sK1,sK0)
    | ~ spl12_29 ),
    inference(avatar_component_clause,[],[f277])).

fof(f113,plain,(
    ! [X3] :
      ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = g1_pre_topc(u1_struct_0(X3),u1_pre_topc(X3))
      | ~ m1_pre_topc(sK1,X3)
      | ~ m1_pre_topc(X3,sK0)
      | ~ v1_tdlat_3(X3)
      | v2_struct_0(X3)
      | v4_tex_2(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f323,plain,
    ( spl12_38
    | ~ spl12_4
    | ~ spl12_26 ),
    inference(avatar_split_clause,[],[f316,f273,f196,f321])).

fof(f316,plain,
    ( l1_pre_topc(sK1)
    | ~ spl12_4
    | ~ spl12_26 ),
    inference(subsumption_resolution,[],[f313,f197])).

fof(f313,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl12_26 ),
    inference(resolution,[],[f127,f274])).

fof(f312,plain,
    ( ~ spl12_29
    | ~ spl12_37
    | ~ spl12_30 ),
    inference(avatar_split_clause,[],[f305,f286,f310,f277])).

fof(f305,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_tex_2(sK1,sK0)
    | ~ spl12_30 ),
    inference(subsumption_resolution,[],[f114,f287])).

fof(f114,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v1_tdlat_3(sK1)
    | ~ v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f288,plain,
    ( spl12_28
    | spl12_30 ),
    inference(avatar_split_clause,[],[f112,f286,f280])).

fof(f112,plain,
    ( v1_tdlat_3(sK1)
    | v4_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f275,plain,(
    spl12_26 ),
    inference(avatar_split_clause,[],[f111,f273])).

fof(f111,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f205,plain,(
    ~ spl12_7 ),
    inference(avatar_split_clause,[],[f110,f203])).

fof(f110,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

fof(f198,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f109,f196])).

fof(f109,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f191,plain,(
    spl12_2 ),
    inference(avatar_split_clause,[],[f108,f189])).

fof(f108,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f83])).

fof(f184,plain,(
    ~ spl12_1 ),
    inference(avatar_split_clause,[],[f107,f182])).

fof(f107,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f83])).
%------------------------------------------------------------------------------
