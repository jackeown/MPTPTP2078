%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:32 EST 2020

% Result     : Theorem 4.94s
% Output     : Refutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :  805 (2118 expanded)
%              Number of leaves         :  134 ( 989 expanded)
%              Depth                    :   20
%              Number of atoms          : 4949 (9240 expanded)
%              Number of equality atoms :  174 ( 760 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f177,f180,f184,f188,f192,f196,f205,f209,f218,f231,f239,f245,f258,f265,f269,f273,f277,f291,f302,f306,f317,f321,f333,f337,f341,f358,f389,f393,f397,f424,f430,f435,f475,f530,f540,f547,f551,f556,f561,f626,f775,f832,f834,f838,f842,f859,f876,f997,f1020,f1026,f1044,f1134,f1295,f1299,f1315,f1330,f1481,f1519,f1563,f1569,f1575,f1602,f1678,f1758,f1763,f1780,f1938,f2075,f2079,f2219,f2370,f2433,f2480,f2493,f2722,f2763,f3617,f3929,f3941,f3963,f3982,f4050,f4218,f4230,f4253,f4371,f4408,f4549,f4557,f4583,f4623,f4958,f5093,f5118,f5652,f5950,f6097,f6377,f6485,f6520,f6562,f6567,f6585,f6590,f6612,f6640,f6677,f6922,f6947,f6962,f6982,f7206,f7270,f7271,f7272,f7288,f7397])).

fof(f7397,plain,
    ( ~ spl5_359
    | ~ spl5_361
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_282
    | spl5_356
    | ~ spl5_362
    | ~ spl5_366
    | ~ spl5_408 ),
    inference(avatar_split_clause,[],[f7332,f6960,f6610,f6565,f6483,f4406,f705,f559,f387,f156,f128,f124,f6554,f6548])).

fof(f6548,plain,
    ( spl5_359
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_359])])).

fof(f6554,plain,
    ( spl5_361
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_361])])).

fof(f124,plain,
    ( spl5_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f128,plain,
    ( spl5_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f156,plain,
    ( spl5_10
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f387,plain,
    ( spl5_53
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f559,plain,
    ( spl5_68
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f705,plain,
    ( spl5_77
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f4406,plain,
    ( spl5_282
  <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_282])])).

fof(f6483,plain,
    ( spl5_356
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_356])])).

fof(f6565,plain,
    ( spl5_362
  <=> ! [X12] : v1_funct_2(k1_xboole_0,X12,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_362])])).

fof(f6610,plain,
    ( spl5_366
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_366])])).

fof(f6960,plain,
    ( spl5_408
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_408])])).

fof(f7332,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_282
    | spl5_356
    | ~ spl5_362
    | ~ spl5_366
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7313,f4407])).

fof(f4407,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_282 ),
    inference(avatar_component_clause,[],[f4406])).

fof(f7313,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | spl5_356
    | ~ spl5_362
    | ~ spl5_366
    | ~ spl5_408 ),
    inference(backward_demodulation,[],[f7299,f6611])).

fof(f6611,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_366 ),
    inference(avatar_component_clause,[],[f6610])).

fof(f7299,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | spl5_356
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7298,f7269])).

fof(f7269,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl5_356 ),
    inference(avatar_component_clause,[],[f6483])).

fof(f7298,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7283,f388])).

fof(f388,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f387])).

fof(f7283,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7282,f388])).

fof(f7282,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7281,f6566])).

fof(f6566,plain,
    ( ! [X12] : v1_funct_2(k1_xboole_0,X12,k1_xboole_0)
    | ~ spl5_362 ),
    inference(avatar_component_clause,[],[f6565])).

fof(f7281,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f7280,f388])).

fof(f7280,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7279,f157])).

fof(f157,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f156])).

fof(f7279,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7278,f157])).

fof(f7278,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7277,f706])).

fof(f706,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f705])).

fof(f7277,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_68
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7276,f129])).

fof(f129,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f7276,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_68
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f7274,f125])).

fof(f125,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f124])).

fof(f7274,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_68
    | ~ spl5_408 ),
    inference(resolution,[],[f6961,f560])).

fof(f560,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ v2_pre_topc(X0) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f559])).

fof(f6961,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_408 ),
    inference(avatar_component_clause,[],[f6960])).

fof(f7288,plain,
    ( spl5_194
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(avatar_split_clause,[],[f7235,f6565,f3159,f840,f705,f559,f387,f156,f136,f132,f128,f124,f2724])).

fof(f2724,plain,
    ( spl5_194
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).

fof(f132,plain,
    ( spl5_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f136,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f840,plain,
    ( spl5_82
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).

fof(f3159,plain,
    ( spl5_204
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).

fof(f7235,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7234,f388])).

fof(f7234,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7233,f6566])).

fof(f7233,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7232,f3160])).

fof(f3160,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_204 ),
    inference(avatar_component_clause,[],[f3159])).

fof(f7232,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7231,f388])).

fof(f7231,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7230,f6566])).

fof(f7230,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(forward_demodulation,[],[f7229,f388])).

fof(f7229,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7228,f133])).

fof(f133,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f7228,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7227,f157])).

fof(f7227,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7226,f157])).

fof(f7226,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7225,f706])).

fof(f7225,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7224,f129])).

fof(f7224,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7223,f125])).

fof(f7223,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7221,f137])).

fof(f137,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f7221,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(resolution,[],[f841,f560])).

fof(f841,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_82 ),
    inference(avatar_component_clause,[],[f840])).

fof(f7272,plain,
    ( ~ spl5_210
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(avatar_split_clause,[],[f7268,f6565,f3159,f2724,f2720,f705,f614,f395,f387,f175,f156,f136,f132,f3608])).

fof(f3608,plain,
    ( spl5_210
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).

fof(f175,plain,
    ( spl5_15
  <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f395,plain,
    ( spl5_55
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f614,plain,
    ( spl5_73
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f2720,plain,
    ( spl5_193
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).

fof(f7268,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7267,f6566])).

fof(f7267,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7266,f3160])).

fof(f7266,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194
    | ~ spl5_204
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7265,f6566])).

fof(f7265,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f7264,f3160])).

fof(f7264,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7263,f133])).

fof(f7263,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_10
    | spl5_15
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7262,f7208])).

fof(f7208,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl5_15
    | ~ spl5_53
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f7207,f615])).

fof(f615,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f614])).

fof(f7207,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl5_15
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f176,f388])).

fof(f176,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f7262,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7261,f157])).

fof(f7261,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7260,f157])).

fof(f7260,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7259,f706])).

fof(f7259,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_193
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7258,f2721])).

fof(f2721,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_193 ),
    inference(avatar_component_clause,[],[f2720])).

fof(f7258,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_194 ),
    inference(subsumption_resolution,[],[f7248,f137])).

fof(f7248,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_55
    | ~ spl5_194 ),
    inference(resolution,[],[f2725,f396])).

fof(f396,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f395])).

fof(f2725,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_194 ),
    inference(avatar_component_clause,[],[f2724])).

fof(f7271,plain,
    ( spl5_408
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(avatar_split_clause,[],[f7246,f6565,f840,f705,f395,f387,f156,f136,f132,f128,f124,f6960])).

fof(f7246,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7245,f6566])).

fof(f7245,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7244,f388])).

fof(f7244,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7243,f6566])).

fof(f7243,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(forward_demodulation,[],[f7242,f388])).

fof(f7242,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7241,f133])).

fof(f7241,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7240,f157])).

fof(f7240,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7239,f157])).

fof(f7239,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7238,f706])).

fof(f7238,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7237,f129])).

fof(f7237,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7236,f125])).

fof(f7236,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f7222,f137])).

fof(f7222,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_55
    | ~ spl5_82 ),
    inference(resolution,[],[f841,f396])).

fof(f7270,plain,
    ( ~ spl5_356
    | spl5_15
    | ~ spl5_53
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f7208,f614,f387,f175,f6483])).

fof(f7206,plain,
    ( spl5_194
    | ~ spl5_210
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_204
    | ~ spl5_356
    | ~ spl5_362 ),
    inference(avatar_split_clause,[],[f7204,f6565,f6483,f3159,f2720,f705,f391,f156,f136,f132,f3608,f2724])).

fof(f391,plain,
    ( spl5_54
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f7204,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_204
    | ~ spl5_356
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7203,f6566])).

fof(f7203,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_204
    | ~ spl5_356
    | ~ spl5_362 ),
    inference(forward_demodulation,[],[f7202,f3160])).

fof(f7202,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_204
    | ~ spl5_356
    | ~ spl5_362 ),
    inference(subsumption_resolution,[],[f7201,f6566])).

fof(f7201,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_204
    | ~ spl5_356 ),
    inference(forward_demodulation,[],[f7200,f3160])).

fof(f7200,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f7199,f133])).

fof(f7199,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f7198,f157])).

fof(f7198,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f7197,f157])).

fof(f7197,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_193
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f7196,f706])).

fof(f7196,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_193
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f7195,f2721])).

fof(f7195,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_356 ),
    inference(subsumption_resolution,[],[f6486,f137])).

fof(f6486,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_54
    | ~ spl5_356 ),
    inference(resolution,[],[f6484,f392])).

fof(f392,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f391])).

fof(f6484,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_356 ),
    inference(avatar_component_clause,[],[f6483])).

fof(f6982,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(avatar_contradiction_clause,[],[f6981])).

fof(f6981,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6980,f6566])).

fof(f6980,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f6979,f388])).

fof(f6979,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_362
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6978,f6566])).

fof(f6978,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_53
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_408 ),
    inference(forward_demodulation,[],[f6977,f388])).

fof(f6977,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | spl5_82
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6976,f2074])).

fof(f2074,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl5_82 ),
    inference(avatar_component_clause,[],[f840])).

fof(f6976,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6975,f133])).

fof(f6975,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6974,f157])).

fof(f6974,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6973,f157])).

fof(f6973,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_77
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6972,f706])).

fof(f6972,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6971,f129])).

fof(f6971,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6970,f125])).

fof(f6970,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(subsumption_resolution,[],[f6967,f137])).

fof(f6967,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_54
    | ~ spl5_408 ),
    inference(resolution,[],[f6961,f392])).

fof(f6962,plain,
    ( ~ spl5_365
    | spl5_408
    | ~ spl5_359
    | ~ spl5_282
    | ~ spl5_356
    | ~ spl5_366
    | ~ spl5_406 ),
    inference(avatar_split_clause,[],[f6954,f6945,f6610,f6483,f4406,f6548,f6960,f6583])).

fof(f6583,plain,
    ( spl5_365
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_365])])).

fof(f6945,plain,
    ( spl5_406
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_406])])).

fof(f6954,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_282
    | ~ spl5_356
    | ~ spl5_366
    | ~ spl5_406 ),
    inference(subsumption_resolution,[],[f6953,f4407])).

fof(f6953,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_356
    | ~ spl5_366
    | ~ spl5_406 ),
    inference(forward_demodulation,[],[f6952,f6611])).

fof(f6952,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_356
    | ~ spl5_406 ),
    inference(resolution,[],[f6946,f6484])).

fof(f6946,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_406 ),
    inference(avatar_component_clause,[],[f6945])).

fof(f6947,plain,
    ( spl5_406
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_402 ),
    inference(avatar_split_clause,[],[f6932,f6920,f6565,f705,f156,f6945])).

fof(f6920,plain,
    ( spl5_402
  <=> ! [X3,X2,X4] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_402])])).

fof(f6932,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_402 ),
    inference(subsumption_resolution,[],[f6931,f157])).

fof(f6931,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_362
    | ~ spl5_402 ),
    inference(subsumption_resolution,[],[f6930,f6566])).

fof(f6930,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_402 ),
    inference(subsumption_resolution,[],[f6927,f157])).

fof(f6927,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_77
    | ~ spl5_402 ),
    inference(resolution,[],[f6921,f706])).

fof(f6921,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl5_402 ),
    inference(avatar_component_clause,[],[f6920])).

fof(f6922,plain,
    ( spl5_402
    | ~ spl5_24
    | ~ spl5_372 ),
    inference(avatar_split_clause,[],[f6680,f6675,f216,f6920])).

fof(f216,plain,
    ( spl5_24
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f6675,plain,
    ( spl5_372
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_372])])).

fof(f6680,plain,
    ( ! [X4,X2,X3] :
        ( ~ v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0)
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl5_24
    | ~ spl5_372 ),
    inference(resolution,[],[f6676,f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f216])).

fof(f6676,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_372 ),
    inference(avatar_component_clause,[],[f6675])).

fof(f6677,plain,
    ( spl5_372
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(avatar_split_clause,[],[f6510,f554,f387,f289,f128,f124,f6675])).

fof(f289,plain,
    ( spl5_38
  <=> ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f554,plain,
    ( spl5_67
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | v5_pre_topc(X3,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f6510,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(forward_demodulation,[],[f6509,f290])).

fof(f290,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f289])).

fof(f6509,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f6508,f129])).

fof(f6508,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f6503,f125])).

fof(f6503,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(superposition,[],[f555,f388])).

fof(f555,plain,
    ( ! [X0,X3,X1] :
        ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
        | ~ v2_pre_topc(X0)
        | v5_pre_topc(X3,X0,X1) )
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f554])).

fof(f6640,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_77
    | spl5_82
    | ~ spl5_194
    | ~ spl5_350
    | ~ spl5_362 ),
    inference(avatar_contradiction_clause,[],[f6636])).

fof(f6636,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_77
    | spl5_82
    | ~ spl5_194
    | ~ spl5_350
    | ~ spl5_362 ),
    inference(unit_resulting_resolution,[],[f137,f133,f706,f2074,f157,f6566,f2725,f5651])).

fof(f5651,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_350 ),
    inference(avatar_component_clause,[],[f5650])).

fof(f5650,plain,
    ( spl5_350
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_350])])).

fof(f6612,plain,
    ( spl5_366
    | ~ spl5_10
    | ~ spl5_34
    | ~ spl5_83
    | ~ spl5_358 ),
    inference(avatar_split_clause,[],[f6527,f6518,f857,f263,f156,f6610])).

% (31174)Time limit reached!
% (31174)------------------------------
% (31174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f263,plain,
    ( spl5_34
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

% (31174)Termination reason: Time limit
% (31174)Termination phase: Saturation
fof(f857,plain,
    ( spl5_83
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

% (31174)Memory used [KB]: 9083
% (31174)Time elapsed: 0.520 s
% (31174)------------------------------
% (31174)------------------------------
fof(f6518,plain,
    ( spl5_358
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_358])])).

fof(f6527,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl5_10
    | ~ spl5_34
    | ~ spl5_83
    | ~ spl5_358 ),
    inference(forward_demodulation,[],[f6526,f858])).

fof(f858,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f857])).

fof(f6526,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl5_10
    | ~ spl5_34
    | ~ spl5_358 ),
    inference(subsumption_resolution,[],[f6521,f157])).

fof(f6521,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl5_34
    | ~ spl5_358 ),
    inference(superposition,[],[f6519,f264])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f263])).

fof(f6519,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl5_358 ),
    inference(avatar_component_clause,[],[f6518])).

fof(f6590,plain,
    ( ~ spl5_5
    | ~ spl5_22
    | spl5_365 ),
    inference(avatar_contradiction_clause,[],[f6589])).

fof(f6589,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_22
    | spl5_365 ),
    inference(subsumption_resolution,[],[f6587,f137])).

fof(f6587,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_22
    | spl5_365 ),
    inference(resolution,[],[f6584,f208])).

fof(f208,plain,
    ( ! [X0] :
        ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f207])).

fof(f207,plain,
    ( spl5_22
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f6584,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl5_365 ),
    inference(avatar_component_clause,[],[f6583])).

fof(f6585,plain,
    ( ~ spl5_365
    | ~ spl5_24
    | spl5_361 ),
    inference(avatar_split_clause,[],[f6563,f6554,f216,f6583])).

fof(f6563,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_24
    | spl5_361 ),
    inference(resolution,[],[f6555,f217])).

fof(f6555,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_361 ),
    inference(avatar_component_clause,[],[f6554])).

fof(f6567,plain,
    ( spl5_362
    | ~ spl5_18
    | ~ spl5_83
    | ~ spl5_256
    | ~ spl5_302 ),
    inference(avatar_split_clause,[],[f6064,f4621,f4228,f857,f190,f6565])).

fof(f190,plain,
    ( spl5_18
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f4228,plain,
    ( spl5_256
  <=> ! [X1,X0,X2] :
        ( v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_256])])).

fof(f4621,plain,
    ( spl5_302
  <=> ! [X16,X15] : k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_302])])).

fof(f6064,plain,
    ( ! [X12] : v1_funct_2(k1_xboole_0,X12,k1_xboole_0)
    | ~ spl5_18
    | ~ spl5_83
    | ~ spl5_256
    | ~ spl5_302 ),
    inference(subsumption_resolution,[],[f4644,f191])).

fof(f191,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f4644,plain,
    ( ! [X12] :
        ( k1_xboole_0 != X12
        | v1_funct_2(k1_xboole_0,X12,k1_xboole_0) )
    | ~ spl5_83
    | ~ spl5_256
    | ~ spl5_302 ),
    inference(forward_demodulation,[],[f4637,f858])).

fof(f4637,plain,
    ( ! [X12] :
        ( k1_relat_1(k1_xboole_0) != X12
        | v1_funct_2(k1_xboole_0,X12,k1_xboole_0) )
    | ~ spl5_256
    | ~ spl5_302 ),
    inference(superposition,[],[f4229,f4622])).

fof(f4622,plain,
    ( ! [X15,X16] : k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16)
    | ~ spl5_302 ),
    inference(avatar_component_clause,[],[f4621])).

fof(f4229,plain,
    ( ! [X2,X0,X1] :
        ( k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) )
    | ~ spl5_256 ),
    inference(avatar_component_clause,[],[f4228])).

fof(f6562,plain,
    ( ~ spl5_4
    | ~ spl5_5
    | ~ spl5_29
    | spl5_359 ),
    inference(avatar_contradiction_clause,[],[f6561])).

fof(f6561,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_29
    | spl5_359 ),
    inference(subsumption_resolution,[],[f6560,f133])).

fof(f6560,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_29
    | spl5_359 ),
    inference(subsumption_resolution,[],[f6558,f137])).

fof(f6558,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_29
    | spl5_359 ),
    inference(resolution,[],[f6549,f238])).

fof(f238,plain,
    ( ! [X0] :
        ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f237])).

fof(f237,plain,
    ( spl5_29
  <=> ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f6549,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl5_359 ),
    inference(avatar_component_clause,[],[f6548])).

fof(f6520,plain,
    ( spl5_204
    | spl5_358
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_53
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f6470,f836,f387,f356,f168,f160,f140,f6518,f3159])).

fof(f140,plain,
    ( spl5_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f160,plain,
    ( spl5_11
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f168,plain,
    ( spl5_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f356,plain,
    ( spl5_50
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f836,plain,
    ( spl5_81
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f6470,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_6
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_53
    | ~ spl5_81 ),
    inference(backward_demodulation,[],[f6414,f6454])).

fof(f6454,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_6
    | ~ spl5_81 ),
    inference(backward_demodulation,[],[f141,f837])).

fof(f837,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f836])).

fof(f141,plain,
    ( sK2 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f140])).

fof(f6414,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f6234,f388])).

fof(f6234,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f382,f388])).

fof(f382,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f379,f169])).

fof(f169,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f168])).

fof(f379,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_11
    | ~ spl5_50 ),
    inference(resolution,[],[f357,f161])).

fof(f161,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f357,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f356])).

fof(f6485,plain,
    ( spl5_356
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_53
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f6468,f836,f387,f175,f140,f6483])).

fof(f6468,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_6
    | ~ spl5_15
    | ~ spl5_53
    | ~ spl5_81 ),
    inference(backward_demodulation,[],[f6363,f6454])).

fof(f6363,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_15
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f179,f388])).

fof(f179,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f175])).

fof(f6377,plain,
    ( ~ spl5_9
    | ~ spl5_38
    | ~ spl5_53
    | spl5_72 ),
    inference(avatar_contradiction_clause,[],[f6376])).

fof(f6376,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_38
    | ~ spl5_53
    | spl5_72 ),
    inference(subsumption_resolution,[],[f612,f6328])).

fof(f6328,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_9
    | ~ spl5_38
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f6327,f290])).

fof(f6327,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl5_9
    | ~ spl5_53 ),
    inference(forward_demodulation,[],[f153,f388])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl5_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f612,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl5_72 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl5_72
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f6097,plain,
    ( ~ spl5_13
    | ~ spl5_38
    | spl5_72
    | ~ spl5_75 ),
    inference(avatar_contradiction_clause,[],[f6096])).

fof(f6096,plain,
    ( $false
    | ~ spl5_13
    | ~ spl5_38
    | spl5_72
    | ~ spl5_75 ),
    inference(subsumption_resolution,[],[f612,f5984])).

fof(f5984,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_13
    | ~ spl5_38
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f5983,f290])).

fof(f5983,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl5_13
    | ~ spl5_75 ),
    inference(forward_demodulation,[],[f169,f622])).

fof(f622,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_75 ),
    inference(avatar_component_clause,[],[f621])).

fof(f621,plain,
    ( spl5_75
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).

fof(f5950,plain,
    ( ~ spl5_73
    | ~ spl5_83
    | spl5_107
    | ~ spl5_282 ),
    inference(avatar_contradiction_clause,[],[f5949])).

fof(f5949,plain,
    ( $false
    | ~ spl5_73
    | ~ spl5_83
    | spl5_107
    | ~ spl5_282 ),
    inference(subsumption_resolution,[],[f5948,f4407])).

fof(f5948,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_73
    | ~ spl5_83
    | spl5_107 ),
    inference(forward_demodulation,[],[f5947,f858])).

fof(f5947,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_73
    | spl5_107 ),
    inference(forward_demodulation,[],[f1394,f615])).

fof(f1394,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl5_107 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f1297,plain,
    ( spl5_107
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).

fof(f5652,plain,
    ( spl5_350
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(avatar_split_clause,[],[f5492,f3159,f554,f387,f289,f128,f124,f5650])).

fof(f5492,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(duplicate_literal_removal,[],[f5491])).

fof(f5491,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f5490,f290])).

fof(f5490,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f5489,f3160])).

fof(f5489,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(duplicate_literal_removal,[],[f5488])).

fof(f5488,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67
    | ~ spl5_204 ),
    inference(forward_demodulation,[],[f5487,f3160])).

fof(f5487,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_38
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(forward_demodulation,[],[f5486,f290])).

fof(f5486,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f5485,f129])).

fof(f5485,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_2
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f5480,f125])).

fof(f5480,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0)))
        | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
        | ~ v2_pre_topc(X1)
        | v5_pre_topc(X0,X1,sK1) )
    | ~ spl5_53
    | ~ spl5_67 ),
    inference(superposition,[],[f555,f388])).

fof(f5118,plain,
    ( ~ spl5_125
    | spl5_88
    | ~ spl5_121
    | ~ spl5_75
    | ~ spl5_158
    | ~ spl5_173
    | ~ spl5_344 ),
    inference(avatar_split_clause,[],[f5104,f5091,f2217,f2077,f621,f1545,f905,f1567])).

fof(f1567,plain,
    ( spl5_125
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).

fof(f905,plain,
    ( spl5_88
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).

fof(f1545,plain,
    ( spl5_121
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).

fof(f2077,plain,
    ( spl5_158
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).

fof(f2217,plain,
    ( spl5_173
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).

fof(f5091,plain,
    ( spl5_344
  <=> ! [X1,X0] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_344])])).

fof(f5104,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_75
    | ~ spl5_158
    | ~ spl5_173
    | ~ spl5_344 ),
    inference(subsumption_resolution,[],[f5103,f2078])).

fof(f2078,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl5_158 ),
    inference(avatar_component_clause,[],[f2077])).

fof(f5103,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_75
    | ~ spl5_173
    | ~ spl5_344 ),
    inference(forward_demodulation,[],[f5099,f622])).

fof(f5099,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_173
    | ~ spl5_344 ),
    inference(resolution,[],[f5092,f2218])).

fof(f2218,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_173 ),
    inference(avatar_component_clause,[],[f2217])).

fof(f5092,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_344 ),
    inference(avatar_component_clause,[],[f5091])).

fof(f5093,plain,
    ( spl5_344
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_331 ),
    inference(avatar_split_clause,[],[f4967,f4956,f705,f156,f5091])).

fof(f4956,plain,
    ( spl5_331
  <=> ! [X3,X2,X4] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v1_funct_1(X2)
        | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_331])])).

fof(f4967,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_331 ),
    inference(subsumption_resolution,[],[f4966,f157])).

fof(f4966,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_331 ),
    inference(subsumption_resolution,[],[f4963,f157])).

fof(f4963,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1))
        | ~ v2_pre_topc(g1_pre_topc(X0,X1))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1)))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
    | ~ spl5_77
    | ~ spl5_331 ),
    inference(resolution,[],[f4957,f706])).

fof(f4957,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))
        | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl5_331 ),
    inference(avatar_component_clause,[],[f4956])).

fof(f4958,plain,
    ( spl5_331
    | ~ spl5_24
    | ~ spl5_231 ),
    inference(avatar_split_clause,[],[f3932,f3927,f216,f4956])).

fof(f3927,plain,
    ( spl5_231
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).

fof(f3932,plain,
    ( ! [X4,X2,X3] :
        ( ~ v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4))
        | ~ v2_pre_topc(g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4)))))
        | ~ v1_funct_1(X2)
        | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))) )
    | ~ spl5_24
    | ~ spl5_231 ),
    inference(resolution,[],[f3928,f217])).

fof(f3928,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_231 ),
    inference(avatar_component_clause,[],[f3927])).

fof(f4623,plain,
    ( spl5_302
    | ~ spl5_21
    | ~ spl5_300 ),
    inference(avatar_split_clause,[],[f4599,f4581,f203,f4621])).

fof(f203,plain,
    ( spl5_21
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f4581,plain,
    ( spl5_300
  <=> ! [X9,X8] : v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_300])])).

fof(f4599,plain,
    ( ! [X15,X16] : k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16)
    | ~ spl5_21
    | ~ spl5_300 ),
    inference(resolution,[],[f4582,f204])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f4582,plain,
    ( ! [X8,X9] : v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9))
    | ~ spl5_300 ),
    inference(avatar_component_clause,[],[f4581])).

fof(f4583,plain,
    ( spl5_300
    | ~ spl5_27
    | ~ spl5_297 ),
    inference(avatar_split_clause,[],[f4571,f4555,f229,f4581])).

fof(f229,plain,
    ( spl5_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f4555,plain,
    ( spl5_297
  <=> ! [X1,X0] : m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_297])])).

fof(f4571,plain,
    ( ! [X8,X9] : v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9))
    | ~ spl5_27
    | ~ spl5_297 ),
    inference(resolution,[],[f4556,f230])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f4556,plain,
    ( ! [X0,X1] : m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_297 ),
    inference(avatar_component_clause,[],[f4555])).

fof(f4557,plain,
    ( spl5_297
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_296 ),
    inference(avatar_split_clause,[],[f4553,f4547,f705,f156,f4555])).

fof(f4547,plain,
    ( spl5_296
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_296])])).

fof(f4553,plain,
    ( ! [X0,X1] : m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_296 ),
    inference(subsumption_resolution,[],[f4550,f157])).

fof(f4550,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_77
    | ~ spl5_296 ),
    inference(resolution,[],[f4548,f706])).

fof(f4548,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl5_296 ),
    inference(avatar_component_clause,[],[f4547])).

fof(f4549,plain,
    ( spl5_296
    | ~ spl5_38
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f372,f339,f289,f4547])).

fof(f339,plain,
    ( spl5_47
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) )
    | ~ spl5_38
    | ~ spl5_47 ),
    inference(superposition,[],[f340,f290])).

fof(f340,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f339])).

fof(f4408,plain,
    ( spl5_282
    | ~ spl5_10
    | ~ spl5_44
    | ~ spl5_77
    | ~ spl5_242
    | ~ spl5_277 ),
    inference(avatar_split_clause,[],[f4385,f4369,f4048,f705,f319,f156,f4406])).

fof(f319,plain,
    ( spl5_44
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f4048,plain,
    ( spl5_242
  <=> ! [X11] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).

fof(f4369,plain,
    ( spl5_277
  <=> ! [X1,X0] : v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_277])])).

fof(f4385,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_44
    | ~ spl5_77
    | ~ spl5_242
    | ~ spl5_277 ),
    inference(forward_demodulation,[],[f4384,f4049])).

fof(f4049,plain,
    ( ! [X11] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X11)
    | ~ spl5_242 ),
    inference(avatar_component_clause,[],[f4048])).

fof(f4384,plain,
    ( ! [X0,X1] : v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_44
    | ~ spl5_77
    | ~ spl5_277 ),
    inference(subsumption_resolution,[],[f4383,f706])).

fof(f4383,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_10
    | ~ spl5_44
    | ~ spl5_277 ),
    inference(subsumption_resolution,[],[f4382,f157])).

fof(f4382,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_44
    | ~ spl5_277 ),
    inference(superposition,[],[f4370,f320])).

fof(f320,plain,
    ( ! [X2,X0,X3,X1] :
        ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f319])).

fof(f4370,plain,
    ( ! [X0,X1] : v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)
    | ~ spl5_277 ),
    inference(avatar_component_clause,[],[f4369])).

fof(f4371,plain,
    ( spl5_277
    | ~ spl5_10
    | ~ spl5_47
    | ~ spl5_77
    | ~ spl5_259 ),
    inference(avatar_split_clause,[],[f4356,f4251,f705,f339,f156,f4369])).

fof(f4251,plain,
    ( spl5_259
  <=> ! [X1,X3,X0,X2] :
        ( k1_xboole_0 != X0
        | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | ~ m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).

fof(f4356,plain,
    ( ! [X0,X1] : v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)
    | ~ spl5_10
    | ~ spl5_47
    | ~ spl5_77
    | ~ spl5_259 ),
    inference(subsumption_resolution,[],[f4355,f706])).

fof(f4355,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_10
    | ~ spl5_47
    | ~ spl5_259 ),
    inference(subsumption_resolution,[],[f4354,f157])).

fof(f4354,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_47
    | ~ spl5_259 ),
    inference(trivial_inequality_removal,[],[f4351])).

fof(f4351,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)
        | k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | ~ v1_funct_1(k1_xboole_0) )
    | ~ spl5_47
    | ~ spl5_259 ),
    inference(resolution,[],[f4252,f340])).

fof(f4252,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
        | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | k1_xboole_0 != X0 )
    | ~ spl5_259 ),
    inference(avatar_component_clause,[],[f4251])).

fof(f4253,plain,
    ( spl5_259
    | ~ spl5_45
    | ~ spl5_256 ),
    inference(avatar_split_clause,[],[f4240,f4228,f331,f4251])).

fof(f331,plain,
    ( spl5_45
  <=> ! [X7,X8] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8)))
        | k1_xboole_0 = k1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f4240,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_xboole_0 != X0
        | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | ~ m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) )
    | ~ spl5_45
    | ~ spl5_256 ),
    inference(superposition,[],[f4229,f332])).

fof(f332,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 = k1_relat_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8))) )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f331])).

fof(f4230,plain,
    ( spl5_256
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_254 ),
    inference(avatar_split_clause,[],[f4226,f4216,f705,f156,f4228])).

fof(f4216,plain,
    ( spl5_254
  <=> ! [X1,X3,X0,X2] :
        ( k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).

fof(f4226,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0 )
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_254 ),
    inference(subsumption_resolution,[],[f4223,f157])).

fof(f4223,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0 )
    | ~ spl5_77
    | ~ spl5_254 ),
    inference(resolution,[],[f4217,f706])).

fof(f4217,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0 )
    | ~ spl5_254 ),
    inference(avatar_component_clause,[],[f4216])).

fof(f4218,plain,
    ( spl5_254
    | ~ spl5_34
    | ~ spl5_47
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f1684,f1676,f339,f263,f4216])).

fof(f1676,plain,
    ( spl5_142
  <=> ! [X1,X3,X0,X2] :
        ( k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f1684,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_34
    | ~ spl5_47
    | ~ spl5_142 ),
    inference(subsumption_resolution,[],[f1682,f340])).

fof(f1682,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_34
    | ~ spl5_142 ),
    inference(superposition,[],[f1677,f264])).

fof(f1677,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f1676])).

fof(f4050,plain,
    ( spl5_242
    | ~ spl5_21
    | ~ spl5_237 ),
    inference(avatar_split_clause,[],[f4000,f3980,f203,f4048])).

fof(f3980,plain,
    ( spl5_237
  <=> ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).

fof(f4000,plain,
    ( ! [X11] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X11)
    | ~ spl5_21
    | ~ spl5_237 ),
    inference(resolution,[],[f3981,f204])).

fof(f3981,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))
    | ~ spl5_237 ),
    inference(avatar_component_clause,[],[f3980])).

fof(f3982,plain,
    ( spl5_237
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_235 ),
    inference(avatar_split_clause,[],[f3974,f3961,f705,f156,f3980])).

fof(f3961,plain,
    ( spl5_235
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X2)
        | v1_xboole_0(k7_relat_1(X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).

fof(f3974,plain,
    ( ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))
    | ~ spl5_10
    | ~ spl5_77
    | ~ spl5_235 ),
    inference(subsumption_resolution,[],[f3971,f157])).

fof(f3971,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(k7_relat_1(k1_xboole_0,X0)) )
    | ~ spl5_77
    | ~ spl5_235 ),
    inference(resolution,[],[f3962,f706])).

fof(f3962,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(k7_relat_1(X2,X3)) )
    | ~ spl5_235 ),
    inference(avatar_component_clause,[],[f3961])).

fof(f3963,plain,
    ( spl5_235
    | ~ spl5_27
    | ~ spl5_232 ),
    inference(avatar_split_clause,[],[f3947,f3939,f229,f3961])).

fof(f3939,plain,
    ( spl5_232
  <=> ! [X1,X2] :
        ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).

fof(f3947,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X2)
        | v1_xboole_0(k7_relat_1(X2,X3)) )
    | ~ spl5_27
    | ~ spl5_232 ),
    inference(resolution,[],[f3940,f230])).

fof(f3940,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) )
    | ~ spl5_232 ),
    inference(avatar_component_clause,[],[f3939])).

fof(f3941,plain,
    ( spl5_232
    | ~ spl5_38
    | ~ spl5_97 ),
    inference(avatar_split_clause,[],[f1022,f1018,f289,f3939])).

fof(f1018,plain,
    ( spl5_97
  <=> ! [X1,X3,X0,X2] :
        ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1022,plain,
    ( ! [X2,X1] :
        ( m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_1(X1) )
    | ~ spl5_38
    | ~ spl5_97 ),
    inference(superposition,[],[f1019,f290])).

fof(f1019,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f1018])).

fof(f3929,plain,
    ( spl5_231
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(avatar_split_clause,[],[f3433,f995,f857,f614,f433,f391,f136,f132,f3927])).

fof(f433,plain,
    ( spl5_58
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f995,plain,
    ( spl5_94
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f3433,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f3432,f858])).

fof(f3432,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f3431,f615])).

fof(f3431,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f3430,f858])).

fof(f3430,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(forward_demodulation,[],[f3429,f615])).

fof(f3429,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83
    | ~ spl5_94 ),
    inference(subsumption_resolution,[],[f3428,f996])).

fof(f996,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f995])).

fof(f3428,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3427,f858])).

fof(f3427,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3426,f615])).

fof(f3426,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3425,f858])).

fof(f3425,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3424,f615])).

fof(f3424,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73
    | ~ spl5_83 ),
    inference(forward_demodulation,[],[f3423,f858])).

fof(f3423,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_73 ),
    inference(forward_demodulation,[],[f568,f615])).

fof(f568,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f567,f133])).

fof(f567,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_5
    | ~ spl5_54
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f566,f137])).

fof(f566,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_54
    | ~ spl5_58 ),
    inference(superposition,[],[f392,f434])).

fof(f434,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_58 ),
    inference(avatar_component_clause,[],[f433])).

fof(f3617,plain,
    ( ~ spl5_197
    | ~ spl5_24
    | spl5_210 ),
    inference(avatar_split_clause,[],[f3612,f3608,f216,f2761])).

fof(f2761,plain,
    ( spl5_197
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).

fof(f3612,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_24
    | spl5_210 ),
    inference(resolution,[],[f3609,f217])).

fof(f3609,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl5_210 ),
    inference(avatar_component_clause,[],[f3608])).

fof(f2763,plain,
    ( spl5_197
    | ~ spl5_3
    | ~ spl5_22
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f2698,f387,f207,f128,f2761])).

fof(f2698,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ spl5_3
    | ~ spl5_22
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f2687,f129])).

fof(f2687,plain,
    ( m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))
    | ~ l1_pre_topc(sK1)
    | ~ spl5_22
    | ~ spl5_53 ),
    inference(superposition,[],[f208,f388])).

fof(f2722,plain,
    ( spl5_193
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_29
    | ~ spl5_53 ),
    inference(avatar_split_clause,[],[f2695,f387,f237,f128,f124,f2720])).

fof(f2695,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_29
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f2694,f125])).

fof(f2694,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ spl5_3
    | ~ spl5_29
    | ~ spl5_53 ),
    inference(subsumption_resolution,[],[f2685,f129])).

fof(f2685,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_29
    | ~ spl5_53 ),
    inference(superposition,[],[f238,f388])).

fof(f2493,plain,
    ( spl5_88
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85
    | ~ spl5_93
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f2492,f1024,f991,f874,f840,f705,f621,f559,f156,f136,f132,f128,f124,f905])).

fof(f874,plain,
    ( spl5_85
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).

fof(f991,plain,
    ( spl5_93
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f1024,plain,
    ( spl5_98
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f2492,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85
    | ~ spl5_93
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2491,f992])).

fof(f992,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f991])).

fof(f2491,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f2490,f875])).

fof(f875,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_85 ),
    inference(avatar_component_clause,[],[f874])).

fof(f2490,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f2489,f622])).

fof(f2489,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2488,f1025])).

fof(f1025,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f1024])).

fof(f2488,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82
    | ~ spl5_85 ),
    inference(forward_demodulation,[],[f2487,f875])).

fof(f2487,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2486,f133])).

fof(f2486,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2485,f157])).

fof(f2485,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2484,f157])).

fof(f2484,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_77
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2483,f706])).

fof(f2483,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2482,f129])).

fof(f2482,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2481,f125])).

fof(f2481,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(subsumption_resolution,[],[f2464,f137])).

fof(f2464,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_68
    | ~ spl5_82 ),
    inference(resolution,[],[f841,f560])).

fof(f2480,plain,
    ( ~ spl5_120
    | ~ spl5_121
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | spl5_15
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107
    | ~ spl5_158 ),
    inference(avatar_split_clause,[],[f2432,f2077,f1297,f905,f874,f857,f836,f705,f621,f614,f395,f175,f156,f140,f136,f132,f1545,f1542])).

fof(f1542,plain,
    ( spl5_120
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).

fof(f2432,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | spl5_15
    | ~ spl5_55
    | ~ spl5_73
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107
    | ~ spl5_158 ),
    inference(subsumption_resolution,[],[f2399,f2420])).

fof(f2420,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_15
    | ~ spl5_73
    | ~ spl5_85 ),
    inference(forward_demodulation,[],[f2419,f615])).

fof(f2419,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_15
    | ~ spl5_85 ),
    inference(forward_demodulation,[],[f176,f875])).

fof(f2399,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107
    | ~ spl5_158 ),
    inference(forward_demodulation,[],[f2398,f875])).

fof(f2398,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107
    | ~ spl5_158 ),
    inference(subsumption_resolution,[],[f2397,f2078])).

fof(f2397,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107 ),
    inference(forward_demodulation,[],[f2396,f875])).

fof(f2396,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107 ),
    inference(forward_demodulation,[],[f2395,f622])).

fof(f2395,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f2388,f2394])).

fof(f2394,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_75
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_107 ),
    inference(forward_demodulation,[],[f1919,f858])).

fof(f1919,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_75
    | ~ spl5_81
    | ~ spl5_107 ),
    inference(backward_demodulation,[],[f1812,f622])).

fof(f1812,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_6
    | ~ spl5_81
    | ~ spl5_107 ),
    inference(backward_demodulation,[],[f1298,f1792])).

fof(f1792,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_6
    | ~ spl5_81 ),
    inference(backward_demodulation,[],[f141,f837])).

fof(f1298,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_107 ),
    inference(avatar_component_clause,[],[f1297])).

fof(f2388,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_85
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f2387,f875])).

fof(f2387,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_75
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f2386,f622])).

fof(f2386,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2385,f133])).

fof(f2385,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2384,f157])).

fof(f2384,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2383,f157])).

fof(f2383,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2382,f706])).

fof(f2382,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_55
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2356,f137])).

fof(f2356,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_55
    | ~ spl5_88 ),
    inference(resolution,[],[f906,f396])).

fof(f906,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_88 ),
    inference(avatar_component_clause,[],[f905])).

fof(f2433,plain,
    ( spl5_93
    | ~ spl5_6
    | ~ spl5_75
    | ~ spl5_81
    | ~ spl5_83
    | ~ spl5_107 ),
    inference(avatar_split_clause,[],[f2394,f1297,f857,f836,f621,f140,f991])).

fof(f2370,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_75
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_93
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f2369])).

fof(f2369,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_75
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_93
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2368,f992])).

fof(f2368,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_75
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f2367,f875])).

fof(f2367,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_75
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_98 ),
    inference(forward_demodulation,[],[f2366,f622])).

fof(f2366,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f2365,f1025])).

fof(f2365,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | spl5_82
    | ~ spl5_85
    | ~ spl5_88 ),
    inference(forward_demodulation,[],[f2364,f875])).

fof(f2364,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | spl5_82
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2363,f2074])).

fof(f2363,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2362,f133])).

fof(f2362,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2361,f157])).

fof(f2361,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_10
    | ~ spl5_67
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2360,f157])).

fof(f2360,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_67
    | ~ spl5_77
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2359,f706])).

fof(f2359,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_67
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2358,f129])).

fof(f2358,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_67
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2357,f125])).

fof(f2357,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_5
    | ~ spl5_67
    | ~ spl5_88 ),
    inference(subsumption_resolution,[],[f2354,f137])).

fof(f2354,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(sK0)
    | v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_67
    | ~ spl5_88 ),
    inference(resolution,[],[f906,f555])).

fof(f2219,plain,
    ( spl5_173
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_45
    | ~ spl5_62
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f2017,f836,f528,f331,f156,f140,f2217])).

fof(f528,plain,
    ( spl5_62
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f2017,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_45
    | ~ spl5_62
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f2016,f157])).

fof(f2016,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) )
    | ~ spl5_6
    | ~ spl5_45
    | ~ spl5_62
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f1939,f1792])).

fof(f1939,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_6
    | ~ spl5_45
    | ~ spl5_62
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f1523,f1792])).

fof(f1523,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_45
    | ~ spl5_62 ),
    inference(superposition,[],[f1518,f332])).

fof(f1518,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f528])).

fof(f2079,plain,
    ( spl5_158
    | ~ spl5_6
    | ~ spl5_75
    | ~ spl5_81
    | ~ spl5_103 ),
    inference(avatar_split_clause,[],[f1977,f1132,f836,f621,f140,f2077])).

fof(f1132,plain,
    ( spl5_103
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).

fof(f1977,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl5_6
    | ~ spl5_75
    | ~ spl5_81
    | ~ spl5_103 ),
    inference(forward_demodulation,[],[f1976,f1792])).

fof(f1976,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl5_75
    | ~ spl5_103 ),
    inference(forward_demodulation,[],[f1133,f622])).

fof(f1133,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_103 ),
    inference(avatar_component_clause,[],[f1132])).

fof(f2075,plain,
    ( ~ spl5_82
    | ~ spl5_6
    | spl5_14
    | ~ spl5_81 ),
    inference(avatar_split_clause,[],[f1794,f836,f172,f140,f840])).

fof(f172,plain,
    ( spl5_14
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1794,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_6
    | spl5_14
    | ~ spl5_81 ),
    inference(backward_demodulation,[],[f173,f1792])).

fof(f173,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1938,plain,
    ( ~ spl5_6
    | ~ spl5_10
    | ~ spl5_45
    | spl5_74
    | ~ spl5_81 ),
    inference(avatar_contradiction_clause,[],[f1937])).

fof(f1937,plain,
    ( $false
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_45
    | spl5_74
    | ~ spl5_81 ),
    inference(subsumption_resolution,[],[f1936,f157])).

fof(f1936,plain,
    ( ! [X0] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl5_6
    | ~ spl5_45
    | spl5_74
    | ~ spl5_81 ),
    inference(forward_demodulation,[],[f1461,f1792])).

fof(f1461,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ spl5_45
    | spl5_74 ),
    inference(trivial_inequality_removal,[],[f1460])).

fof(f1460,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_45
    | spl5_74 ),
    inference(superposition,[],[f1457,f332])).

fof(f1457,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl5_74 ),
    inference(avatar_component_clause,[],[f617])).

fof(f617,plain,
    ( spl5_74
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f1780,plain,
    ( spl5_110
    | ~ spl5_119
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_108 ),
    inference(avatar_split_clause,[],[f1779,f1313,f1297,f1293,f554,f528,f473,f428,f422,f128,f124,f120,f1473,f1328])).

fof(f1328,plain,
    ( spl5_110
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f1473,plain,
    ( spl5_119
  <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).

fof(f120,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f422,plain,
    ( spl5_56
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f428,plain,
    ( spl5_57
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f473,plain,
    ( spl5_60
  <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1293,plain,
    ( spl5_106
  <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).

fof(f1313,plain,
    ( spl5_108
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).

fof(f1779,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_108 ),
    inference(subsumption_resolution,[],[f1778,f1314])).

fof(f1314,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_108 ),
    inference(avatar_component_clause,[],[f1313])).

fof(f1778,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106
    | ~ spl5_107 ),
    inference(forward_demodulation,[],[f1777,f1294])).

fof(f1294,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_106 ),
    inference(avatar_component_clause,[],[f1293])).

fof(f1777,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106
    | ~ spl5_107 ),
    inference(subsumption_resolution,[],[f1776,f1298])).

fof(f1776,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1775,f1294])).

fof(f1775,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106 ),
    inference(subsumption_resolution,[],[f1774,f429])).

fof(f429,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl5_57 ),
    inference(avatar_component_clause,[],[f428])).

fof(f1774,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1773,f1294])).

fof(f1773,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106 ),
    inference(subsumption_resolution,[],[f1772,f423])).

fof(f423,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1772,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67
    | ~ spl5_106 ),
    inference(forward_demodulation,[],[f1771,f1294])).

fof(f1771,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_60
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1770,f474])).

fof(f474,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f473])).

fof(f1770,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1769,f121])).

fof(f121,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f120])).

fof(f1769,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1768,f129])).

fof(f1768,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_2
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(subsumption_resolution,[],[f1520,f125])).

fof(f1520,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_62
    | ~ spl5_67 ),
    inference(resolution,[],[f1518,f555])).

fof(f1763,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_14
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_110
    | ~ spl5_157 ),
    inference(avatar_contradiction_clause,[],[f1759])).

fof(f1759,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | spl5_14
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_110
    | ~ spl5_157 ),
    inference(unit_resulting_resolution,[],[f125,f121,f129,f173,f423,f429,f1329,f1757])).

fof(f1757,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_157 ),
    inference(avatar_component_clause,[],[f1756])).

fof(f1756,plain,
    ( spl5_157
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).

fof(f1329,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f1758,plain,
    ( spl5_157
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1278,f624,f545,f433,f391,f263,f136,f132,f1756])).

fof(f545,plain,
    ( spl5_65
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f624,plain,
    ( spl5_76
  <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).

fof(f1278,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(duplicate_literal_removal,[],[f1277])).

fof(f1277,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1276,f1264])).

fof(f1264,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_34
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1257,f546])).

fof(f546,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f545])).

fof(f1257,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_34
    | ~ spl5_76 ),
    inference(superposition,[],[f625,f264])).

fof(f625,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl5_76 ),
    inference(avatar_component_clause,[],[f624])).

fof(f1276,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(duplicate_literal_removal,[],[f1267])).

fof(f1267,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1))))
        | v5_pre_topc(X0,sK0,X1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_34
    | ~ spl5_54
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f568,f1264])).

fof(f1678,plain,
    ( spl5_142
    | ~ spl5_47
    | ~ spl5_100 ),
    inference(avatar_split_clause,[],[f1428,f1042,f339,f1676])).

fof(f1042,plain,
    ( spl5_100
  <=> ! [X3,X5,X7,X2,X4,X6] :
        ( ~ m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6
        | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).

fof(f1428,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_47
    | ~ spl5_100 ),
    inference(duplicate_literal_removal,[],[f1424])).

fof(f1424,plain,
    ( ! [X2,X0,X3,X1] :
        ( k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0
        | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_47
    | ~ spl5_100 ),
    inference(resolution,[],[f1043,f340])).

fof(f1043,plain,
    ( ! [X6,X4,X2,X7,X5,X3] :
        ( ~ m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6
        | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl5_100 ),
    inference(avatar_component_clause,[],[f1042])).

fof(f1602,plain,
    ( spl5_62
    | ~ spl5_119
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_108
    | ~ spl5_110 ),
    inference(avatar_split_clause,[],[f1514,f1328,f1313,f1297,f1293,f559,f473,f428,f422,f128,f124,f120,f1473,f528])).

fof(f1514,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_108
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1513,f1314])).

fof(f1513,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1512,f1294])).

fof(f1512,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_107
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1511,f1298])).

fof(f1511,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1510,f1294])).

fof(f1510,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1509,f429])).

fof(f1509,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1508,f1294])).

fof(f1508,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_56
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1507,f423])).

fof(f1507,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_106
    | ~ spl5_110 ),
    inference(forward_demodulation,[],[f1506,f1294])).

fof(f1506,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_60
    | ~ spl5_68
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1336,f474])).

fof(f1336,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_68
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1335,f121])).

fof(f1335,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_68
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1334,f129])).

fof(f1334,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_2
    | ~ spl5_68
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1331,f125])).

fof(f1331,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_68
    | ~ spl5_110 ),
    inference(resolution,[],[f1329,f560])).

fof(f1575,plain,
    ( ~ spl5_3
    | ~ spl5_22
    | spl5_125 ),
    inference(avatar_contradiction_clause,[],[f1574])).

fof(f1574,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_22
    | spl5_125 ),
    inference(subsumption_resolution,[],[f1572,f129])).

fof(f1572,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl5_22
    | spl5_125 ),
    inference(resolution,[],[f1568,f208])).

fof(f1568,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl5_125 ),
    inference(avatar_component_clause,[],[f1567])).

fof(f1569,plain,
    ( ~ spl5_125
    | ~ spl5_24
    | spl5_120 ),
    inference(avatar_split_clause,[],[f1557,f1542,f216,f1567])).

fof(f1557,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | ~ spl5_24
    | spl5_120 ),
    inference(resolution,[],[f1543,f217])).

fof(f1543,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_120 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f1563,plain,
    ( ~ spl5_2
    | ~ spl5_3
    | ~ spl5_29
    | spl5_121 ),
    inference(avatar_contradiction_clause,[],[f1562])).

fof(f1562,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_29
    | spl5_121 ),
    inference(subsumption_resolution,[],[f1561,f125])).

fof(f1561,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl5_3
    | ~ spl5_29
    | spl5_121 ),
    inference(subsumption_resolution,[],[f1559,f129])).

fof(f1559,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_29
    | spl5_121 ),
    inference(resolution,[],[f1546,f238])).

fof(f1546,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_121 ),
    inference(avatar_component_clause,[],[f1545])).

fof(f1519,plain,
    ( spl5_62
    | ~ spl5_15
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f1515,f433,f175,f528])).

fof(f1515,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_15
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f179,f434])).

fof(f1481,plain,
    ( ~ spl5_24
    | ~ spl5_66
    | spl5_119 ),
    inference(avatar_contradiction_clause,[],[f1480])).

fof(f1480,plain,
    ( $false
    | ~ spl5_24
    | ~ spl5_66
    | spl5_119 ),
    inference(subsumption_resolution,[],[f1477,f550])).

fof(f550,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f549])).

fof(f549,plain,
    ( spl5_66
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f1477,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl5_24
    | spl5_119 ),
    inference(resolution,[],[f1474,f217])).

fof(f1474,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl5_119 ),
    inference(avatar_component_clause,[],[f1473])).

fof(f1330,plain,
    ( spl5_110
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1281,f624,f545,f433,f428,f422,f395,f263,f172,f136,f132,f128,f124,f120,f1328])).

fof(f1281,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1280,f429])).

fof(f1280,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(forward_demodulation,[],[f1279,f1264])).

fof(f1279,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(subsumption_resolution,[],[f1268,f423])).

fof(f1268,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_34
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f581,f1264])).

fof(f581,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f580,f434])).

fof(f580,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f579,f434])).

fof(f579,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f578,f434])).

fof(f578,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_57
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f577,f429])).

fof(f577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f576,f434])).

fof(f576,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_56
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f575,f423])).

fof(f575,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55
    | ~ spl5_58 ),
    inference(forward_demodulation,[],[f574,f434])).

fof(f574,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f573,f133])).

fof(f573,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f572,f121])).

fof(f572,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f571,f129])).

fof(f571,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f570,f125])).

fof(f570,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f569,f137])).

fof(f569,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))))
    | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_14
    | ~ spl5_55 ),
    inference(resolution,[],[f396,f178])).

fof(f178,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f1315,plain,
    ( spl5_108
    | ~ spl5_34
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1266,f624,f545,f263,f1313])).

fof(f1266,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_34
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f546,f1264])).

fof(f1299,plain,
    ( spl5_107
    | ~ spl5_34
    | ~ spl5_64
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1265,f624,f545,f538,f263,f1297])).

fof(f538,plain,
    ( spl5_64
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f1265,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_34
    | ~ spl5_64
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(backward_demodulation,[],[f539,f1264])).

fof(f539,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f538])).

fof(f1295,plain,
    ( spl5_106
    | ~ spl5_34
    | ~ spl5_65
    | ~ spl5_76 ),
    inference(avatar_split_clause,[],[f1264,f624,f545,f263,f1293])).

fof(f1134,plain,
    ( spl5_103
    | ~ spl5_64
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f1060,f617,f538,f1132])).

fof(f1060,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_64
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f539,f618])).

fof(f618,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f617])).

fof(f1044,plain,
    ( spl5_100
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f366,f335,f275,f1042])).

fof(f275,plain,
    ( spl5_37
  <=> ! [X1,X3,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f335,plain,
    ( spl5_46
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f366,plain,
    ( ! [X6,X4,X2,X7,X5,X3] :
        ( ~ m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6
        | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_1(X4) )
    | ~ spl5_37
    | ~ spl5_46 ),
    inference(resolution,[],[f336,f276])).

fof(f276,plain,
    ( ! [X2,X0,X3,X1] :
        ( v1_funct_1(k2_partfun1(X0,X1,X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f275])).

fof(f336,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) )
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f335])).

fof(f1026,plain,
    ( spl5_98
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_45
    | ~ spl5_56
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f814,f773,f422,f331,f203,f156,f1024])).

fof(f773,plain,
    ( spl5_79
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f814,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl5_10
    | ~ spl5_21
    | ~ spl5_45
    | ~ spl5_56
    | ~ spl5_79 ),
    inference(subsumption_resolution,[],[f813,f157])).

fof(f813,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) )
    | ~ spl5_21
    | ~ spl5_45
    | ~ spl5_56
    | ~ spl5_79 ),
    inference(forward_demodulation,[],[f788,f782])).

fof(f782,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(resolution,[],[f774,f204])).

fof(f774,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f773])).

fof(f788,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_21
    | ~ spl5_45
    | ~ spl5_56
    | ~ spl5_79 ),
    inference(backward_demodulation,[],[f426,f782])).

fof(f426,plain,
    ( ! [X0] :
        ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_45
    | ~ spl5_56 ),
    inference(superposition,[],[f423,f332])).

fof(f1020,plain,
    ( spl5_97
    | ~ spl5_44
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f373,f339,f319,f1018])).

fof(f373,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_44
    | ~ spl5_47 ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,
    ( ! [X2,X0,X3,X1] :
        ( m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl5_44
    | ~ spl5_47 ),
    inference(superposition,[],[f340,f320])).

fof(f997,plain,
    ( spl5_94
    | ~ spl5_21
    | ~ spl5_34
    | ~ spl5_41
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f329,f315,f304,f263,f203,f995])).

fof(f304,plain,
    ( spl5_41
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f315,plain,
    ( spl5_43
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(k1_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f329,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl5_21
    | ~ spl5_34
    | ~ spl5_41
    | ~ spl5_43 ),
    inference(subsumption_resolution,[],[f328,f325])).

fof(f325,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8)))
        | k1_xboole_0 = k1_relat_1(X7) )
    | ~ spl5_21
    | ~ spl5_43 ),
    inference(resolution,[],[f316,f204])).

fof(f316,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k1_relat_1(X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) )
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f315])).

fof(f328,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl5_34
    | ~ spl5_41 ),
    inference(duplicate_literal_removal,[],[f327])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl5_34
    | ~ spl5_41 ),
    inference(superposition,[],[f305,f264])).

fof(f305,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f304])).

fof(f876,plain,
    ( spl5_85
    | ~ spl5_58
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f711,f617,f433,f874])).

fof(f711,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl5_58
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f434,f618])).

fof(f859,plain,
    ( spl5_83
    | ~ spl5_21
    | ~ spl5_74
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f795,f773,f617,f203,f857])).

fof(f795,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_21
    | ~ spl5_74
    | ~ spl5_79 ),
    inference(backward_demodulation,[],[f618,f782])).

fof(f842,plain,
    ( spl5_82
    | ~ spl5_14
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f786,f773,f203,f172,f840])).

fof(f786,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl5_14
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(backward_demodulation,[],[f178,f782])).

fof(f838,plain,
    ( spl5_81
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f785,f773,f203,f140,f836])).

fof(f785,plain,
    ( k1_xboole_0 = sK3
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(backward_demodulation,[],[f141,f782])).

fof(f834,plain,
    ( spl5_73
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f782,f773,f203,f614])).

fof(f832,plain,
    ( spl5_77
    | ~ spl5_1
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(avatar_split_clause,[],[f784,f773,f203,f120,f705])).

fof(f784,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_21
    | ~ spl5_79 ),
    inference(backward_demodulation,[],[f121,f782])).

fof(f775,plain,
    ( spl5_79
    | ~ spl5_27
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f765,f611,f229,f773])).

fof(f765,plain,
    ( v1_xboole_0(sK2)
    | ~ spl5_27
    | ~ spl5_72 ),
    inference(resolution,[],[f763,f230])).

fof(f763,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f611])).

fof(f626,plain,
    ( spl5_75
    | spl5_76
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f510,f433,f356,f168,f160,f624,f621])).

fof(f510,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl5_11
    | ~ spl5_13
    | ~ spl5_50
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f382,f434])).

fof(f561,plain,(
    spl5_68 ),
    inference(avatar_split_clause,[],[f112,f559])).

fof(f112,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f556,plain,(
    spl5_67 ),
    inference(avatar_split_clause,[],[f111,f554])).

fof(f111,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f101])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f551,plain,
    ( spl5_66
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f521,f433,f207,f136,f549])).

fof(f521,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f518,f137])).

fof(f518,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_22
    | ~ spl5_58 ),
    inference(superposition,[],[f208,f434])).

fof(f547,plain,
    ( spl5_65
    | ~ spl5_13
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f508,f433,f168,f545])).

fof(f508,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl5_13
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f169,f434])).

fof(f540,plain,
    ( spl5_64
    | ~ spl5_11
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f507,f433,f160,f538])).

fof(f507,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl5_11
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f161,f434])).

fof(f530,plain,
    ( ~ spl5_62
    | spl5_15
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f509,f433,f175,f528])).

fof(f509,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl5_15
    | ~ spl5_58 ),
    inference(backward_demodulation,[],[f176,f434])).

fof(f475,plain,
    ( spl5_60
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_29
    | ~ spl5_58 ),
    inference(avatar_split_clause,[],[f465,f433,f237,f136,f132,f473])).

fof(f465,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_29
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f464,f133])).

fof(f464,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl5_5
    | ~ spl5_29
    | ~ spl5_58 ),
    inference(subsumption_resolution,[],[f461,f137])).

fof(f461,plain,
    ( v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_29
    | ~ spl5_58 ),
    inference(superposition,[],[f238,f434])).

fof(f435,plain,
    ( spl5_58
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f405,f384,f263,f152,f433])).

fof(f384,plain,
    ( spl5_52
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f405,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(subsumption_resolution,[],[f398,f153])).

fof(f398,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(superposition,[],[f385,f264])).

fof(f385,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f384])).

fof(f430,plain,
    ( spl5_57
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f407,f384,f263,f152,f428])).

fof(f407,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f153,f405])).

fof(f424,plain,
    ( spl5_56
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f406,f384,f263,f152,f144,f422])).

fof(f144,plain,
    ( spl5_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f406,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_34
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f145,f405])).

fof(f145,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f144])).

fof(f397,plain,(
    spl5_55 ),
    inference(avatar_split_clause,[],[f110,f395])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f393,plain,(
    spl5_54 ),
    inference(avatar_split_clause,[],[f109,f391])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f389,plain,
    ( spl5_52
    | spl5_53
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f381,f356,f152,f144,f387,f384])).

fof(f381,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl5_7
    | ~ spl5_9
    | ~ spl5_50 ),
    inference(subsumption_resolution,[],[f378,f153])).

fof(f378,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl5_7
    | ~ spl5_50 ),
    inference(resolution,[],[f357,f145])).

fof(f358,plain,(
    spl5_50 ),
    inference(avatar_split_clause,[],[f94,f356])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f341,plain,(
    spl5_47 ),
    inference(avatar_split_clause,[],[f99,f339])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

fof(f337,plain,(
    spl5_46 ),
    inference(avatar_split_clause,[],[f95,f335])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( k1_relset_1(X0,X1,X2) = X0
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

fof(f333,plain,
    ( spl5_45
    | ~ spl5_21
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f325,f315,f203,f331])).

fof(f321,plain,(
    spl5_44 ),
    inference(avatar_split_clause,[],[f97,f319])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f317,plain,
    ( spl5_43
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f311,f300,f229,f315])).

fof(f300,plain,
    ( spl5_40
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f311,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(k1_relat_1(X0)) )
    | ~ spl5_27
    | ~ spl5_40 ),
    inference(resolution,[],[f301,f230])).

fof(f301,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f300])).

fof(f306,plain,(
    spl5_41 ),
    inference(avatar_split_clause,[],[f105,f304])).

fof(f105,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f302,plain,
    ( spl5_40
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f294,f271,f263,f300])).

fof(f271,plain,
    ( spl5_36
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f294,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(duplicate_literal_removal,[],[f293])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_34
    | ~ spl5_36 ),
    inference(superposition,[],[f272,f264])).

fof(f272,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f271])).

fof(f291,plain,
    ( spl5_38
    | ~ spl5_21
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f280,f267,f203,f289])).

fof(f267,plain,
    ( spl5_35
  <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f280,plain,
    ( ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)
    | ~ spl5_21
    | ~ spl5_35 ),
    inference(resolution,[],[f268,f204])).

fof(f268,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f267])).

fof(f277,plain,(
    spl5_37 ),
    inference(avatar_split_clause,[],[f98,f275])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_1(k2_partfun1(X0,X1,X2,X3)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f273,plain,(
    spl5_36 ),
    inference(avatar_split_clause,[],[f86,f271])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f269,plain,
    ( spl5_35
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f261,f256,f182,f164,f267])).

fof(f164,plain,
    ( spl5_12
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_xboole_0(sK4(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f182,plain,
    ( spl5_16
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f256,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f261,plain,
    ( ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))
    | ~ spl5_12
    | ~ spl5_16
    | ~ spl5_33 ),
    inference(subsumption_resolution,[],[f260,f165])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(sK4(X0))
        | v1_xboole_0(X0) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f164])).

fof(f260,plain,
    ( ! [X0] :
        ( v1_xboole_0(sK4(k2_zfmisc_1(X0,k1_xboole_0)))
        | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0)) )
    | ~ spl5_16
    | ~ spl5_33 ),
    inference(resolution,[],[f257,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(X0),k1_zfmisc_1(X0))
        | v1_xboole_0(X0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f182])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f256])).

fof(f265,plain,(
    spl5_34 ),
    inference(avatar_split_clause,[],[f85,f263])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f258,plain,
    ( spl5_33
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f254,f243,f148,f256])).

fof(f148,plain,
    ( spl5_8
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f243,plain,
    ( spl5_30
  <=> ! [X1,X0,X2] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
        | v1_xboole_0(X0) )
    | ~ spl5_8
    | ~ spl5_30 ),
    inference(resolution,[],[f244,f149])).

fof(f149,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f148])).

fof(f244,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | v1_xboole_0(X2) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f243])).

fof(f245,plain,(
    spl5_30 ),
    inference(avatar_split_clause,[],[f79,f243])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f239,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f74,f237])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f231,plain,
    ( spl5_27
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f227,f194,f148,f229])).

fof(f194,plain,
    ( spl5_19
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl5_8
    | ~ spl5_19 ),
    inference(resolution,[],[f195,f149])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f194])).

fof(f218,plain,(
    spl5_24 ),
    inference(avatar_split_clause,[],[f81,f216])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f209,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f71,f207])).

fof(f71,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f205,plain,
    ( spl5_21
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f201,f186,f148,f203])).

fof(f186,plain,
    ( spl5_17
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f201,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl5_8
    | ~ spl5_17 ),
    inference(resolution,[],[f187,f149])).

fof(f187,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f186])).

fof(f196,plain,(
    spl5_19 ),
    inference(avatar_split_clause,[],[f72,f194])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f192,plain,(
    spl5_18 ),
    inference(avatar_split_clause,[],[f118,f190])).

fof(f118,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(subsumption_resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f108,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | v1_funct_2(k1_xboole_0,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != X2
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f188,plain,(
    spl5_17 ),
    inference(avatar_split_clause,[],[f83,f186])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f184,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f69,f182])).

fof(f69,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).

fof(f180,plain,
    ( spl5_14
    | spl5_15 ),
    inference(avatar_split_clause,[],[f117,f175,f172])).

fof(f117,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f54,f59])).

fof(f59,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f54,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f177,plain,
    ( ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f116,f175,f172])).

fof(f116,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f55,f59])).

fof(f55,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f170,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f113,f168])).

fof(f113,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f58,f59])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f25])).

fof(f166,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f70,f164])).

fof(f70,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ v1_xboole_0(sK4(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f162,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f114,f160])).

fof(f114,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f57,f59])).

fof(f57,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f158,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f68,f156])).

fof(f154,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f62,f152])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f25])).

fof(f150,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f67,f148])).

fof(f67,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f146,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f61,f144])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f142,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f59,f140])).

fof(f138,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f66,f136])).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f134,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f65,f132])).

fof(f65,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f130,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f64,f128])).

fof(f64,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f63,f124])).

fof(f63,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f122,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f60,f120])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:00:44 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (31187)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (31171)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (31176)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (31179)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (31172)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (31169)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (31175)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (31185)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.49  % (31174)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (31186)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.49  % (31182)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (31173)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (31183)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (31170)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (31188)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (31180)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (31184)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (31181)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (31189)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (31179)Refutation not found, incomplete strategy% (31179)------------------------------
% 0.21/0.51  % (31179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31179)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31179)Memory used [KB]: 6524
% 0.21/0.51  % (31179)Time elapsed: 0.100 s
% 0.21/0.51  % (31179)------------------------------
% 0.21/0.51  % (31179)------------------------------
% 0.21/0.51  % (31177)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (31189)Refutation not found, incomplete strategy% (31189)------------------------------
% 0.21/0.51  % (31189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31189)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (31189)Memory used [KB]: 10746
% 0.21/0.51  % (31189)Time elapsed: 0.105 s
% 0.21/0.51  % (31189)------------------------------
% 0.21/0.51  % (31189)------------------------------
% 0.21/0.52  % (31178)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 2.17/0.66  % (31172)Refutation not found, incomplete strategy% (31172)------------------------------
% 2.17/0.66  % (31172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (31172)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (31172)Memory used [KB]: 12025
% 2.17/0.66  % (31172)Time elapsed: 0.233 s
% 2.17/0.66  % (31172)------------------------------
% 2.17/0.66  % (31172)------------------------------
% 4.05/0.92  % (31181)Time limit reached!
% 4.05/0.92  % (31181)------------------------------
% 4.05/0.92  % (31181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.92  % (31181)Termination reason: Time limit
% 4.05/0.92  
% 4.05/0.92  % (31181)Memory used [KB]: 10362
% 4.05/0.92  % (31181)Time elapsed: 0.515 s
% 4.05/0.92  % (31181)------------------------------
% 4.05/0.92  % (31181)------------------------------
% 4.63/0.94  % (31170)Time limit reached!
% 4.63/0.94  % (31170)------------------------------
% 4.63/0.94  % (31170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/0.94  % (31170)Termination reason: Time limit
% 4.63/0.94  
% 4.63/0.94  % (31170)Memory used [KB]: 15607
% 4.63/0.94  % (31170)Time elapsed: 0.525 s
% 4.63/0.94  % (31170)------------------------------
% 4.63/0.94  % (31170)------------------------------
% 4.63/0.94  % (31169)Time limit reached!
% 4.63/0.94  % (31169)------------------------------
% 4.63/0.94  % (31169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.63/0.94  % (31169)Termination reason: Time limit
% 4.63/0.94  % (31169)Termination phase: Saturation
% 4.63/0.94  
% 4.63/0.94  % (31169)Memory used [KB]: 23666
% 4.63/0.94  % (31169)Time elapsed: 0.500 s
% 4.63/0.94  % (31169)------------------------------
% 4.63/0.94  % (31169)------------------------------
% 4.94/0.97  % (31178)Refutation found. Thanks to Tanya!
% 4.94/0.97  % SZS status Theorem for theBenchmark
% 4.94/0.97  % SZS output start Proof for theBenchmark
% 4.94/0.97  fof(f7398,plain,(
% 4.94/0.97    $false),
% 4.94/0.97    inference(avatar_sat_refutation,[],[f122,f126,f130,f134,f138,f142,f146,f150,f154,f158,f162,f166,f170,f177,f180,f184,f188,f192,f196,f205,f209,f218,f231,f239,f245,f258,f265,f269,f273,f277,f291,f302,f306,f317,f321,f333,f337,f341,f358,f389,f393,f397,f424,f430,f435,f475,f530,f540,f547,f551,f556,f561,f626,f775,f832,f834,f838,f842,f859,f876,f997,f1020,f1026,f1044,f1134,f1295,f1299,f1315,f1330,f1481,f1519,f1563,f1569,f1575,f1602,f1678,f1758,f1763,f1780,f1938,f2075,f2079,f2219,f2370,f2433,f2480,f2493,f2722,f2763,f3617,f3929,f3941,f3963,f3982,f4050,f4218,f4230,f4253,f4371,f4408,f4549,f4557,f4583,f4623,f4958,f5093,f5118,f5652,f5950,f6097,f6377,f6485,f6520,f6562,f6567,f6585,f6590,f6612,f6640,f6677,f6922,f6947,f6962,f6982,f7206,f7270,f7271,f7272,f7288,f7397])).
% 4.94/0.97  fof(f7397,plain,(
% 4.94/0.97    ~spl5_359 | ~spl5_361 | ~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_282 | spl5_356 | ~spl5_362 | ~spl5_366 | ~spl5_408),
% 4.94/0.97    inference(avatar_split_clause,[],[f7332,f6960,f6610,f6565,f6483,f4406,f705,f559,f387,f156,f128,f124,f6554,f6548])).
% 4.94/0.97  fof(f6548,plain,(
% 4.94/0.97    spl5_359 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_359])])).
% 4.94/0.97  fof(f6554,plain,(
% 4.94/0.97    spl5_361 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_361])])).
% 4.94/0.97  fof(f124,plain,(
% 4.94/0.97    spl5_2 <=> v2_pre_topc(sK1)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 4.94/0.97  fof(f128,plain,(
% 4.94/0.97    spl5_3 <=> l1_pre_topc(sK1)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 4.94/0.97  fof(f156,plain,(
% 4.94/0.97    spl5_10 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 4.94/0.97  fof(f387,plain,(
% 4.94/0.97    spl5_53 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 4.94/0.97  fof(f559,plain,(
% 4.94/0.97    spl5_68 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 4.94/0.97  fof(f705,plain,(
% 4.94/0.97    spl5_77 <=> v1_funct_1(k1_xboole_0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 4.94/0.97  fof(f4406,plain,(
% 4.94/0.97    spl5_282 <=> ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_282])])).
% 4.94/0.97  fof(f6483,plain,(
% 4.94/0.97    spl5_356 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_356])])).
% 4.94/0.97  fof(f6565,plain,(
% 4.94/0.97    spl5_362 <=> ! [X12] : v1_funct_2(k1_xboole_0,X12,k1_xboole_0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_362])])).
% 4.94/0.97  fof(f6610,plain,(
% 4.94/0.97    spl5_366 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_366])])).
% 4.94/0.97  fof(f6960,plain,(
% 4.94/0.97    spl5_408 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_408])])).
% 4.94/0.97  fof(f7332,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_282 | spl5_356 | ~spl5_362 | ~spl5_366 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7313,f4407])).
% 4.94/0.97  fof(f4407,plain,(
% 4.94/0.97    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl5_282),
% 4.94/0.97    inference(avatar_component_clause,[],[f4406])).
% 4.94/0.97  fof(f7313,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | spl5_356 | ~spl5_362 | ~spl5_366 | ~spl5_408)),
% 4.94/0.97    inference(backward_demodulation,[],[f7299,f6611])).
% 4.94/0.97  fof(f6611,plain,(
% 4.94/0.97    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl5_366),
% 4.94/0.97    inference(avatar_component_clause,[],[f6610])).
% 4.94/0.97  fof(f7299,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | spl5_356 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7298,f7269])).
% 4.94/0.97  fof(f7269,plain,(
% 4.94/0.97    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl5_356),
% 4.94/0.97    inference(avatar_component_clause,[],[f6483])).
% 4.94/0.97  fof(f7298,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(forward_demodulation,[],[f7283,f388])).
% 4.94/0.97  fof(f388,plain,(
% 4.94/0.97    k1_xboole_0 = u1_struct_0(sK1) | ~spl5_53),
% 4.94/0.97    inference(avatar_component_clause,[],[f387])).
% 4.94/0.97  fof(f7283,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(forward_demodulation,[],[f7282,f388])).
% 4.94/0.97  fof(f7282,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7281,f6566])).
% 4.94/0.97  fof(f6566,plain,(
% 4.94/0.97    ( ! [X12] : (v1_funct_2(k1_xboole_0,X12,k1_xboole_0)) ) | ~spl5_362),
% 4.94/0.97    inference(avatar_component_clause,[],[f6565])).
% 4.94/0.97  fof(f7281,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(forward_demodulation,[],[f7280,f388])).
% 4.94/0.97  fof(f7280,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7279,f157])).
% 4.94/0.97  fof(f157,plain,(
% 4.94/0.97    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl5_10),
% 4.94/0.97    inference(avatar_component_clause,[],[f156])).
% 4.94/0.97  fof(f7279,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7278,f157])).
% 4.94/0.97  fof(f7278,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_68 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7277,f706])).
% 4.94/0.97  fof(f706,plain,(
% 4.94/0.97    v1_funct_1(k1_xboole_0) | ~spl5_77),
% 4.94/0.97    inference(avatar_component_clause,[],[f705])).
% 4.94/0.97  fof(f7277,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_68 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7276,f129])).
% 4.94/0.97  fof(f129,plain,(
% 4.94/0.97    l1_pre_topc(sK1) | ~spl5_3),
% 4.94/0.97    inference(avatar_component_clause,[],[f128])).
% 4.94/0.97  fof(f7276,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_68 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7274,f125])).
% 4.94/0.97  fof(f125,plain,(
% 4.94/0.97    v2_pre_topc(sK1) | ~spl5_2),
% 4.94/0.97    inference(avatar_component_clause,[],[f124])).
% 4.94/0.97  fof(f7274,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_68 | ~spl5_408)),
% 4.94/0.97    inference(resolution,[],[f6961,f560])).
% 4.94/0.97  fof(f560,plain,(
% 4.94/0.97    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v2_pre_topc(X0)) ) | ~spl5_68),
% 4.94/0.97    inference(avatar_component_clause,[],[f559])).
% 4.94/0.97  fof(f6961,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl5_408),
% 4.94/0.97    inference(avatar_component_clause,[],[f6960])).
% 4.94/0.97  fof(f7288,plain,(
% 4.94/0.97    spl5_194 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_204 | ~spl5_362),
% 4.94/0.97    inference(avatar_split_clause,[],[f7235,f6565,f3159,f840,f705,f559,f387,f156,f136,f132,f128,f124,f2724])).
% 4.94/0.97  fof(f2724,plain,(
% 4.94/0.97    spl5_194 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_194])])).
% 4.94/0.97  fof(f132,plain,(
% 4.94/0.97    spl5_4 <=> v2_pre_topc(sK0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 4.94/0.97  fof(f136,plain,(
% 4.94/0.97    spl5_5 <=> l1_pre_topc(sK0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 4.94/0.97  fof(f840,plain,(
% 4.94/0.97    spl5_82 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_82])])).
% 4.94/0.97  fof(f3159,plain,(
% 4.94/0.97    spl5_204 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_204])])).
% 4.94/0.97  fof(f7235,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7234,f388])).
% 4.94/0.97  fof(f7234,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7233,f6566])).
% 4.94/0.97  fof(f7233,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7232,f3160])).
% 4.94/0.97  fof(f3160,plain,(
% 4.94/0.97    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl5_204),
% 4.94/0.97    inference(avatar_component_clause,[],[f3159])).
% 4.94/0.97  fof(f7232,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7231,f388])).
% 4.94/0.97  fof(f7231,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7230,f6566])).
% 4.94/0.97  fof(f7230,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(forward_demodulation,[],[f7229,f388])).
% 4.94/0.97  fof(f7229,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7228,f133])).
% 4.94/0.97  fof(f133,plain,(
% 4.94/0.97    v2_pre_topc(sK0) | ~spl5_4),
% 4.94/0.97    inference(avatar_component_clause,[],[f132])).
% 4.94/0.97  fof(f7228,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7227,f157])).
% 4.94/0.97  fof(f7227,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7226,f157])).
% 4.94/0.97  fof(f7226,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7225,f706])).
% 4.94/0.97  fof(f7225,plain,(
% 4.94/0.97    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7224,f129])).
% 4.94/0.97  fof(f7224,plain,(
% 4.94/0.97    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7223,f125])).
% 4.94/0.97  fof(f7223,plain,(
% 4.94/0.97    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7221,f137])).
% 4.94/0.97  fof(f137,plain,(
% 4.94/0.97    l1_pre_topc(sK0) | ~spl5_5),
% 4.94/0.97    inference(avatar_component_clause,[],[f136])).
% 4.94/0.97  fof(f7221,plain,(
% 4.94/0.97    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_68 | ~spl5_82)),
% 4.94/0.97    inference(resolution,[],[f841,f560])).
% 4.94/0.97  fof(f841,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl5_82),
% 4.94/0.97    inference(avatar_component_clause,[],[f840])).
% 4.94/0.97  fof(f7272,plain,(
% 4.94/0.97    ~spl5_210 | ~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194 | ~spl5_204 | ~spl5_362),
% 4.94/0.97    inference(avatar_split_clause,[],[f7268,f6565,f3159,f2724,f2720,f705,f614,f395,f387,f175,f156,f136,f132,f3608])).
% 4.94/0.97  fof(f3608,plain,(
% 4.94/0.97    spl5_210 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_210])])).
% 4.94/0.97  fof(f175,plain,(
% 4.94/0.97    spl5_15 <=> v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 4.94/0.97  fof(f395,plain,(
% 4.94/0.97    spl5_55 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 4.94/0.97  fof(f614,plain,(
% 4.94/0.97    spl5_73 <=> k1_xboole_0 = sK2),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 4.94/0.97  fof(f2720,plain,(
% 4.94/0.97    spl5_193 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_193])])).
% 4.94/0.97  fof(f7268,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7267,f6566])).
% 4.94/0.97  fof(f7267,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7266,f3160])).
% 4.94/0.97  fof(f7266,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194 | ~spl5_204 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7265,f6566])).
% 4.94/0.97  fof(f7265,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194 | ~spl5_204)),
% 4.94/0.97    inference(forward_demodulation,[],[f7264,f3160])).
% 4.94/0.97  fof(f7264,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7263,f133])).
% 4.94/0.97  fof(f7263,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_10 | spl5_15 | ~spl5_53 | ~spl5_55 | ~spl5_73 | ~spl5_77 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7262,f7208])).
% 4.94/0.97  fof(f7208,plain,(
% 4.94/0.97    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl5_15 | ~spl5_53 | ~spl5_73)),
% 4.94/0.97    inference(forward_demodulation,[],[f7207,f615])).
% 4.94/0.97  fof(f615,plain,(
% 4.94/0.97    k1_xboole_0 = sK2 | ~spl5_73),
% 4.94/0.97    inference(avatar_component_clause,[],[f614])).
% 4.94/0.97  fof(f7207,plain,(
% 4.94/0.97    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (spl5_15 | ~spl5_53)),
% 4.94/0.97    inference(forward_demodulation,[],[f176,f388])).
% 4.94/0.97  fof(f176,plain,(
% 4.94/0.97    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_15),
% 4.94/0.97    inference(avatar_component_clause,[],[f175])).
% 4.94/0.97  fof(f7262,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7261,f157])).
% 4.94/0.97  fof(f7261,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7260,f157])).
% 4.94/0.97  fof(f7260,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_77 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7259,f706])).
% 4.94/0.97  fof(f7259,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_193 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7258,f2721])).
% 4.94/0.97  fof(f2721,plain,(
% 4.94/0.97    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl5_193),
% 4.94/0.97    inference(avatar_component_clause,[],[f2720])).
% 4.94/0.97  fof(f7258,plain,(
% 4.94/0.97    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_194)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7248,f137])).
% 4.94/0.97  fof(f7248,plain,(
% 4.94/0.97    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_55 | ~spl5_194)),
% 4.94/0.97    inference(resolution,[],[f2725,f396])).
% 4.94/0.97  fof(f396,plain,(
% 4.94/0.97    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v2_pre_topc(X0)) ) | ~spl5_55),
% 4.94/0.97    inference(avatar_component_clause,[],[f395])).
% 4.94/0.97  fof(f2725,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl5_194),
% 4.94/0.97    inference(avatar_component_clause,[],[f2724])).
% 4.94/0.97  fof(f7271,plain,(
% 4.94/0.97    spl5_408 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_55 | ~spl5_77 | ~spl5_82 | ~spl5_362),
% 4.94/0.97    inference(avatar_split_clause,[],[f7246,f6565,f840,f705,f395,f387,f156,f136,f132,f128,f124,f6960])).
% 4.94/0.97  fof(f7246,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_55 | ~spl5_77 | ~spl5_82 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7245,f6566])).
% 4.94/0.97  fof(f7245,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_55 | ~spl5_77 | ~spl5_82 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7244,f388])).
% 4.94/0.97  fof(f7244,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_55 | ~spl5_77 | ~spl5_82 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7243,f6566])).
% 4.94/0.97  fof(f7243,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_55 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(forward_demodulation,[],[f7242,f388])).
% 4.94/0.97  fof(f7242,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7241,f133])).
% 4.94/0.97  fof(f7241,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7240,f157])).
% 4.94/0.97  fof(f7240,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7239,f157])).
% 4.94/0.97  fof(f7239,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_55 | ~spl5_77 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7238,f706])).
% 4.94/0.97  fof(f7238,plain,(
% 4.94/0.97    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_55 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7237,f129])).
% 4.94/0.97  fof(f7237,plain,(
% 4.94/0.97    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_5 | ~spl5_55 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7236,f125])).
% 4.94/0.97  fof(f7236,plain,(
% 4.94/0.97    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_82)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7222,f137])).
% 4.94/0.97  fof(f7222,plain,(
% 4.94/0.97    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_55 | ~spl5_82)),
% 4.94/0.97    inference(resolution,[],[f841,f396])).
% 4.94/0.97  fof(f7270,plain,(
% 4.94/0.97    ~spl5_356 | spl5_15 | ~spl5_53 | ~spl5_73),
% 4.94/0.97    inference(avatar_split_clause,[],[f7208,f614,f387,f175,f6483])).
% 4.94/0.97  fof(f7206,plain,(
% 4.94/0.97    spl5_194 | ~spl5_210 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_204 | ~spl5_356 | ~spl5_362),
% 4.94/0.97    inference(avatar_split_clause,[],[f7204,f6565,f6483,f3159,f2720,f705,f391,f156,f136,f132,f3608,f2724])).
% 4.94/0.97  fof(f391,plain,(
% 4.94/0.97    spl5_54 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 4.94/0.97  fof(f7204,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_204 | ~spl5_356 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7203,f6566])).
% 4.94/0.97  fof(f7203,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_204 | ~spl5_356 | ~spl5_362)),
% 4.94/0.97    inference(forward_demodulation,[],[f7202,f3160])).
% 4.94/0.97  fof(f7202,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_204 | ~spl5_356 | ~spl5_362)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7201,f6566])).
% 4.94/0.97  fof(f7201,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_204 | ~spl5_356)),
% 4.94/0.97    inference(forward_demodulation,[],[f7200,f3160])).
% 4.94/0.97  fof(f7200,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7199,f133])).
% 4.94/0.97  fof(f7199,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7198,f157])).
% 4.94/0.97  fof(f7198,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7197,f157])).
% 4.94/0.97  fof(f7197,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_5 | ~spl5_54 | ~spl5_77 | ~spl5_193 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7196,f706])).
% 4.94/0.97  fof(f7196,plain,(
% 4.94/0.97    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_5 | ~spl5_54 | ~spl5_193 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f7195,f2721])).
% 4.94/0.97  fof(f7195,plain,(
% 4.94/0.97    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_5 | ~spl5_54 | ~spl5_356)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6486,f137])).
% 4.94/0.97  fof(f6486,plain,(
% 4.94/0.97    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_54 | ~spl5_356)),
% 4.94/0.97    inference(resolution,[],[f6484,f392])).
% 4.94/0.97  fof(f392,plain,(
% 4.94/0.97    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X3,X0,X1)) ) | ~spl5_54),
% 4.94/0.97    inference(avatar_component_clause,[],[f391])).
% 4.94/0.97  fof(f6484,plain,(
% 4.94/0.97    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl5_356),
% 4.94/0.97    inference(avatar_component_clause,[],[f6483])).
% 4.94/0.97  fof(f6982,plain,(
% 4.94/0.97    ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_362 | ~spl5_408),
% 4.94/0.97    inference(avatar_contradiction_clause,[],[f6981])).
% 4.94/0.97  fof(f6981,plain,(
% 4.94/0.97    $false | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6980,f6566])).
% 4.94/0.97  fof(f6980,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(forward_demodulation,[],[f6979,f388])).
% 4.94/0.97  fof(f6979,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_362 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6978,f6566])).
% 4.94/0.97  fof(f6978,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_53 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_408)),
% 4.94/0.97    inference(forward_demodulation,[],[f6977,f388])).
% 4.94/0.97  fof(f6977,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | spl5_82 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6976,f2074])).
% 4.94/0.97  fof(f2074,plain,(
% 4.94/0.97    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl5_82),
% 4.94/0.97    inference(avatar_component_clause,[],[f840])).
% 4.94/0.97  fof(f6976,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6975,f133])).
% 4.94/0.97  fof(f6975,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6974,f157])).
% 4.94/0.97  fof(f6974,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_54 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6973,f157])).
% 4.94/0.97  fof(f6973,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_54 | ~spl5_77 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6972,f706])).
% 4.94/0.97  fof(f6972,plain,(
% 4.94/0.97    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_54 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6971,f129])).
% 4.94/0.97  fof(f6971,plain,(
% 4.94/0.97    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_5 | ~spl5_54 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6970,f125])).
% 4.94/0.97  fof(f6970,plain,(
% 4.94/0.97    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_5 | ~spl5_54 | ~spl5_408)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6967,f137])).
% 4.94/0.97  fof(f6967,plain,(
% 4.94/0.97    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_54 | ~spl5_408)),
% 4.94/0.97    inference(resolution,[],[f6961,f392])).
% 4.94/0.97  fof(f6962,plain,(
% 4.94/0.97    ~spl5_365 | spl5_408 | ~spl5_359 | ~spl5_282 | ~spl5_356 | ~spl5_366 | ~spl5_406),
% 4.94/0.97    inference(avatar_split_clause,[],[f6954,f6945,f6610,f6483,f4406,f6548,f6960,f6583])).
% 4.94/0.97  fof(f6583,plain,(
% 4.94/0.97    spl5_365 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_365])])).
% 4.94/0.97  fof(f6945,plain,(
% 4.94/0.97    spl5_406 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_406])])).
% 4.94/0.97  fof(f6954,plain,(
% 4.94/0.97    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_282 | ~spl5_356 | ~spl5_366 | ~spl5_406)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6953,f4407])).
% 4.94/0.97  fof(f6953,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_356 | ~spl5_366 | ~spl5_406)),
% 4.94/0.97    inference(forward_demodulation,[],[f6952,f6611])).
% 4.94/0.97  fof(f6952,plain,(
% 4.94/0.97    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_356 | ~spl5_406)),
% 4.94/0.97    inference(resolution,[],[f6946,f6484])).
% 4.94/0.97  fof(f6946,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl5_406),
% 4.94/0.97    inference(avatar_component_clause,[],[f6945])).
% 4.94/0.97  fof(f6947,plain,(
% 4.94/0.97    spl5_406 | ~spl5_10 | ~spl5_77 | ~spl5_362 | ~spl5_402),
% 4.94/0.97    inference(avatar_split_clause,[],[f6932,f6920,f6565,f705,f156,f6945])).
% 4.94/0.97  fof(f6920,plain,(
% 4.94/0.97    spl5_402 <=> ! [X3,X2,X4] : (~v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_402])])).
% 4.94/0.97  fof(f6932,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_10 | ~spl5_77 | ~spl5_362 | ~spl5_402)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6931,f157])).
% 4.94/0.97  fof(f6931,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_10 | ~spl5_77 | ~spl5_362 | ~spl5_402)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6930,f6566])).
% 4.94/0.97  fof(f6930,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_10 | ~spl5_77 | ~spl5_402)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6927,f157])).
% 4.94/0.97  fof(f6927,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X0,X1)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X0,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_77 | ~spl5_402)),
% 4.94/0.97    inference(resolution,[],[f6921,f706])).
% 4.94/0.97  fof(f6921,plain,(
% 4.94/0.97    ( ! [X4,X2,X3] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | ~spl5_402),
% 4.94/0.97    inference(avatar_component_clause,[],[f6920])).
% 4.94/0.97  fof(f6922,plain,(
% 4.94/0.97    spl5_402 | ~spl5_24 | ~spl5_372),
% 4.94/0.97    inference(avatar_split_clause,[],[f6680,f6675,f216,f6920])).
% 4.94/0.97  fof(f216,plain,(
% 4.94/0.97    spl5_24 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1)))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 4.94/0.97  fof(f6675,plain,(
% 4.94/0.97    spl5_372 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_372])])).
% 4.94/0.97  fof(f6680,plain,(
% 4.94/0.97    ( ! [X4,X2,X3] : (~v5_pre_topc(X2,g1_pre_topc(X3,X4),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),k1_xboole_0) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X3,X4)),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | v5_pre_topc(X2,g1_pre_topc(X3,X4),sK1) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | (~spl5_24 | ~spl5_372)),
% 4.94/0.97    inference(resolution,[],[f6676,f217])).
% 4.94/0.97  fof(f217,plain,(
% 4.94/0.97    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl5_24),
% 4.94/0.97    inference(avatar_component_clause,[],[f216])).
% 4.94/0.97  fof(f6676,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | ~spl5_372),
% 4.94/0.97    inference(avatar_component_clause,[],[f6675])).
% 4.94/0.97  fof(f6677,plain,(
% 4.94/0.97    spl5_372 | ~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67),
% 4.94/0.97    inference(avatar_split_clause,[],[f6510,f554,f387,f289,f128,f124,f6675])).
% 4.94/0.97  fof(f289,plain,(
% 4.94/0.97    spl5_38 <=> ! [X5] : k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 4.94/0.97  fof(f554,plain,(
% 4.94/0.97    spl5_67 <=> ! [X1,X3,X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1))),
% 4.94/0.97    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 4.94/0.97  fof(f6510,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67)),
% 4.94/0.97    inference(forward_demodulation,[],[f6509,f290])).
% 4.94/0.97  fof(f290,plain,(
% 4.94/0.97    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)) ) | ~spl5_38),
% 4.94/0.97    inference(avatar_component_clause,[],[f289])).
% 4.94/0.97  fof(f6509,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_53 | ~spl5_67)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6508,f129])).
% 4.94/0.97  fof(f6508,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_53 | ~spl5_67)),
% 4.94/0.97    inference(subsumption_resolution,[],[f6503,f125])).
% 4.94/0.97  fof(f6503,plain,(
% 4.94/0.97    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_53 | ~spl5_67)),
% 4.94/0.97    inference(superposition,[],[f555,f388])).
% 4.94/0.98  fof(f555,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v2_pre_topc(X0) | v5_pre_topc(X3,X0,X1)) ) | ~spl5_67),
% 4.94/0.98    inference(avatar_component_clause,[],[f554])).
% 4.94/0.98  fof(f6640,plain,(
% 4.94/0.98    ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_77 | spl5_82 | ~spl5_194 | ~spl5_350 | ~spl5_362),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f6636])).
% 4.94/0.98  fof(f6636,plain,(
% 4.94/0.98    $false | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_77 | spl5_82 | ~spl5_194 | ~spl5_350 | ~spl5_362)),
% 4.94/0.98    inference(unit_resulting_resolution,[],[f137,f133,f706,f2074,f157,f6566,f2725,f5651])).
% 4.94/0.98  fof(f5651,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | ~spl5_350),
% 4.94/0.98    inference(avatar_component_clause,[],[f5650])).
% 4.94/0.98  fof(f5650,plain,(
% 4.94/0.98    spl5_350 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_350])])).
% 4.94/0.98  fof(f6612,plain,(
% 4.94/0.98    spl5_366 | ~spl5_10 | ~spl5_34 | ~spl5_83 | ~spl5_358),
% 4.94/0.98    inference(avatar_split_clause,[],[f6527,f6518,f857,f263,f156,f6610])).
% 4.94/0.98  % (31174)Time limit reached!
% 4.94/0.98  % (31174)------------------------------
% 4.94/0.98  % (31174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/0.98  fof(f263,plain,(
% 4.94/0.98    spl5_34 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 4.94/0.98  % (31174)Termination reason: Time limit
% 4.94/0.98  % (31174)Termination phase: Saturation
% 4.94/0.98  fof(f857,plain,(
% 4.94/0.98    spl5_83 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 4.94/0.98  
% 4.94/0.98  % (31174)Memory used [KB]: 9083
% 4.94/0.98  % (31174)Time elapsed: 0.520 s
% 4.94/0.98  % (31174)------------------------------
% 4.94/0.98  % (31174)------------------------------
% 4.94/0.98  fof(f6518,plain,(
% 4.94/0.98    spl5_358 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_358])])).
% 4.94/0.98  fof(f6527,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl5_10 | ~spl5_34 | ~spl5_83 | ~spl5_358)),
% 4.94/0.98    inference(forward_demodulation,[],[f6526,f858])).
% 4.94/0.98  fof(f858,plain,(
% 4.94/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl5_83),
% 4.94/0.98    inference(avatar_component_clause,[],[f857])).
% 4.94/0.98  fof(f6526,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | (~spl5_10 | ~spl5_34 | ~spl5_358)),
% 4.94/0.98    inference(subsumption_resolution,[],[f6521,f157])).
% 4.94/0.98  fof(f6521,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl5_34 | ~spl5_358)),
% 4.94/0.98    inference(superposition,[],[f6519,f264])).
% 4.94/0.98  fof(f264,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_34),
% 4.94/0.98    inference(avatar_component_clause,[],[f263])).
% 4.94/0.98  fof(f6519,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl5_358),
% 4.94/0.98    inference(avatar_component_clause,[],[f6518])).
% 4.94/0.98  fof(f6590,plain,(
% 4.94/0.98    ~spl5_5 | ~spl5_22 | spl5_365),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f6589])).
% 4.94/0.98  fof(f6589,plain,(
% 4.94/0.98    $false | (~spl5_5 | ~spl5_22 | spl5_365)),
% 4.94/0.98    inference(subsumption_resolution,[],[f6587,f137])).
% 4.94/0.98  fof(f6587,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | (~spl5_22 | spl5_365)),
% 4.94/0.98    inference(resolution,[],[f6584,f208])).
% 4.94/0.98  fof(f208,plain,(
% 4.94/0.98    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) ) | ~spl5_22),
% 4.94/0.98    inference(avatar_component_clause,[],[f207])).
% 4.94/0.98  fof(f207,plain,(
% 4.94/0.98    spl5_22 <=> ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 4.94/0.98  fof(f6584,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl5_365),
% 4.94/0.98    inference(avatar_component_clause,[],[f6583])).
% 4.94/0.98  fof(f6585,plain,(
% 4.94/0.98    ~spl5_365 | ~spl5_24 | spl5_361),
% 4.94/0.98    inference(avatar_split_clause,[],[f6563,f6554,f216,f6583])).
% 4.94/0.98  fof(f6563,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl5_24 | spl5_361)),
% 4.94/0.98    inference(resolution,[],[f6555,f217])).
% 4.94/0.98  fof(f6555,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_361),
% 4.94/0.98    inference(avatar_component_clause,[],[f6554])).
% 4.94/0.98  fof(f6567,plain,(
% 4.94/0.98    spl5_362 | ~spl5_18 | ~spl5_83 | ~spl5_256 | ~spl5_302),
% 4.94/0.98    inference(avatar_split_clause,[],[f6064,f4621,f4228,f857,f190,f6565])).
% 4.94/0.98  fof(f190,plain,(
% 4.94/0.98    spl5_18 <=> ! [X0] : (k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 4.94/0.98  fof(f4228,plain,(
% 4.94/0.98    spl5_256 <=> ! [X1,X0,X2] : (v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_256])])).
% 4.94/0.98  fof(f4621,plain,(
% 4.94/0.98    spl5_302 <=> ! [X16,X15] : k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_302])])).
% 4.94/0.98  fof(f6064,plain,(
% 4.94/0.98    ( ! [X12] : (v1_funct_2(k1_xboole_0,X12,k1_xboole_0)) ) | (~spl5_18 | ~spl5_83 | ~spl5_256 | ~spl5_302)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4644,f191])).
% 4.94/0.98  fof(f191,plain,(
% 4.94/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl5_18),
% 4.94/0.98    inference(avatar_component_clause,[],[f190])).
% 4.94/0.98  fof(f4644,plain,(
% 4.94/0.98    ( ! [X12] : (k1_xboole_0 != X12 | v1_funct_2(k1_xboole_0,X12,k1_xboole_0)) ) | (~spl5_83 | ~spl5_256 | ~spl5_302)),
% 4.94/0.98    inference(forward_demodulation,[],[f4637,f858])).
% 4.94/0.98  fof(f4637,plain,(
% 4.94/0.98    ( ! [X12] : (k1_relat_1(k1_xboole_0) != X12 | v1_funct_2(k1_xboole_0,X12,k1_xboole_0)) ) | (~spl5_256 | ~spl5_302)),
% 4.94/0.98    inference(superposition,[],[f4229,f4622])).
% 4.94/0.98  fof(f4622,plain,(
% 4.94/0.98    ( ! [X15,X16] : (k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16)) ) | ~spl5_302),
% 4.94/0.98    inference(avatar_component_clause,[],[f4621])).
% 4.94/0.98  fof(f4229,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0 | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1)) ) | ~spl5_256),
% 4.94/0.98    inference(avatar_component_clause,[],[f4228])).
% 4.94/0.98  fof(f6562,plain,(
% 4.94/0.98    ~spl5_4 | ~spl5_5 | ~spl5_29 | spl5_359),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f6561])).
% 4.94/0.98  fof(f6561,plain,(
% 4.94/0.98    $false | (~spl5_4 | ~spl5_5 | ~spl5_29 | spl5_359)),
% 4.94/0.98    inference(subsumption_resolution,[],[f6560,f133])).
% 4.94/0.98  fof(f6560,plain,(
% 4.94/0.98    ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_29 | spl5_359)),
% 4.94/0.98    inference(subsumption_resolution,[],[f6558,f137])).
% 4.94/0.98  fof(f6558,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_29 | spl5_359)),
% 4.94/0.98    inference(resolution,[],[f6549,f238])).
% 4.94/0.98  fof(f238,plain,(
% 4.94/0.98    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_29),
% 4.94/0.98    inference(avatar_component_clause,[],[f237])).
% 4.94/0.98  fof(f237,plain,(
% 4.94/0.98    spl5_29 <=> ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 4.94/0.98  fof(f6549,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl5_359),
% 4.94/0.98    inference(avatar_component_clause,[],[f6548])).
% 4.94/0.98  fof(f6520,plain,(
% 4.94/0.98    spl5_204 | spl5_358 | ~spl5_6 | ~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_53 | ~spl5_81),
% 4.94/0.98    inference(avatar_split_clause,[],[f6470,f836,f387,f356,f168,f160,f140,f6518,f3159])).
% 4.94/0.98  fof(f140,plain,(
% 4.94/0.98    spl5_6 <=> sK2 = sK3),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 4.94/0.98  fof(f160,plain,(
% 4.94/0.98    spl5_11 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 4.94/0.98  fof(f168,plain,(
% 4.94/0.98    spl5_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 4.94/0.98  fof(f356,plain,(
% 4.94/0.98    spl5_50 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 4.94/0.98  fof(f836,plain,(
% 4.94/0.98    spl5_81 <=> k1_xboole_0 = sK3),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 4.94/0.98  fof(f6470,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_6 | ~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_53 | ~spl5_81)),
% 4.94/0.98    inference(backward_demodulation,[],[f6414,f6454])).
% 4.94/0.98  fof(f6454,plain,(
% 4.94/0.98    k1_xboole_0 = sK2 | (~spl5_6 | ~spl5_81)),
% 4.94/0.98    inference(backward_demodulation,[],[f141,f837])).
% 4.94/0.98  fof(f837,plain,(
% 4.94/0.98    k1_xboole_0 = sK3 | ~spl5_81),
% 4.94/0.98    inference(avatar_component_clause,[],[f836])).
% 4.94/0.98  fof(f141,plain,(
% 4.94/0.98    sK2 = sK3 | ~spl5_6),
% 4.94/0.98    inference(avatar_component_clause,[],[f140])).
% 4.94/0.98  fof(f6414,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_53)),
% 4.94/0.98    inference(forward_demodulation,[],[f6234,f388])).
% 4.94/0.98  fof(f6234,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_53)),
% 4.94/0.98    inference(forward_demodulation,[],[f382,f388])).
% 4.94/0.98  fof(f382,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl5_11 | ~spl5_13 | ~spl5_50)),
% 4.94/0.98    inference(subsumption_resolution,[],[f379,f169])).
% 4.94/0.98  fof(f169,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_13),
% 4.94/0.98    inference(avatar_component_clause,[],[f168])).
% 4.94/0.98  fof(f379,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_11 | ~spl5_50)),
% 4.94/0.98    inference(resolution,[],[f357,f161])).
% 4.94/0.98  fof(f161,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_11),
% 4.94/0.98    inference(avatar_component_clause,[],[f160])).
% 4.94/0.98  fof(f357,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_50),
% 4.94/0.98    inference(avatar_component_clause,[],[f356])).
% 4.94/0.98  fof(f6485,plain,(
% 4.94/0.98    spl5_356 | ~spl5_6 | ~spl5_15 | ~spl5_53 | ~spl5_81),
% 4.94/0.98    inference(avatar_split_clause,[],[f6468,f836,f387,f175,f140,f6483])).
% 4.94/0.98  fof(f6468,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_6 | ~spl5_15 | ~spl5_53 | ~spl5_81)),
% 4.94/0.98    inference(backward_demodulation,[],[f6363,f6454])).
% 4.94/0.98  fof(f6363,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_15 | ~spl5_53)),
% 4.94/0.98    inference(forward_demodulation,[],[f179,f388])).
% 4.94/0.98  fof(f179,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_15),
% 4.94/0.98    inference(avatar_component_clause,[],[f175])).
% 4.94/0.98  fof(f6377,plain,(
% 4.94/0.98    ~spl5_9 | ~spl5_38 | ~spl5_53 | spl5_72),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f6376])).
% 4.94/0.98  fof(f6376,plain,(
% 4.94/0.98    $false | (~spl5_9 | ~spl5_38 | ~spl5_53 | spl5_72)),
% 4.94/0.98    inference(subsumption_resolution,[],[f612,f6328])).
% 4.94/0.98  fof(f6328,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_9 | ~spl5_38 | ~spl5_53)),
% 4.94/0.98    inference(forward_demodulation,[],[f6327,f290])).
% 4.94/0.98  fof(f6327,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl5_9 | ~spl5_53)),
% 4.94/0.98    inference(forward_demodulation,[],[f153,f388])).
% 4.94/0.98  fof(f153,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl5_9),
% 4.94/0.98    inference(avatar_component_clause,[],[f152])).
% 4.94/0.98  fof(f152,plain,(
% 4.94/0.98    spl5_9 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 4.94/0.98  fof(f612,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl5_72),
% 4.94/0.98    inference(avatar_component_clause,[],[f611])).
% 4.94/0.98  fof(f611,plain,(
% 4.94/0.98    spl5_72 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 4.94/0.98  fof(f6097,plain,(
% 4.94/0.98    ~spl5_13 | ~spl5_38 | spl5_72 | ~spl5_75),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f6096])).
% 4.94/0.98  fof(f6096,plain,(
% 4.94/0.98    $false | (~spl5_13 | ~spl5_38 | spl5_72 | ~spl5_75)),
% 4.94/0.98    inference(subsumption_resolution,[],[f612,f5984])).
% 4.94/0.98  fof(f5984,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_13 | ~spl5_38 | ~spl5_75)),
% 4.94/0.98    inference(forward_demodulation,[],[f5983,f290])).
% 4.94/0.98  fof(f5983,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl5_13 | ~spl5_75)),
% 4.94/0.98    inference(forward_demodulation,[],[f169,f622])).
% 4.94/0.98  fof(f622,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_75),
% 4.94/0.98    inference(avatar_component_clause,[],[f621])).
% 4.94/0.98  fof(f621,plain,(
% 4.94/0.98    spl5_75 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_75])])).
% 4.94/0.98  fof(f5950,plain,(
% 4.94/0.98    ~spl5_73 | ~spl5_83 | spl5_107 | ~spl5_282),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f5949])).
% 4.94/0.98  fof(f5949,plain,(
% 4.94/0.98    $false | (~spl5_73 | ~spl5_83 | spl5_107 | ~spl5_282)),
% 4.94/0.98    inference(subsumption_resolution,[],[f5948,f4407])).
% 4.94/0.98  fof(f5948,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_73 | ~spl5_83 | spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f5947,f858])).
% 4.94/0.98  fof(f5947,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_73 | spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f1394,f615])).
% 4.94/0.98  fof(f1394,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | spl5_107),
% 4.94/0.98    inference(avatar_component_clause,[],[f1297])).
% 4.94/0.98  fof(f1297,plain,(
% 4.94/0.98    spl5_107 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_107])])).
% 4.94/0.98  fof(f5652,plain,(
% 4.94/0.98    spl5_350 | ~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204),
% 4.94/0.98    inference(avatar_split_clause,[],[f5492,f3159,f554,f387,f289,f128,f124,f5650])).
% 4.94/0.98  fof(f5492,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f5491])).
% 4.94/0.98  fof(f5491,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204)),
% 4.94/0.98    inference(forward_demodulation,[],[f5490,f290])).
% 4.94/0.98  fof(f5490,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204)),
% 4.94/0.98    inference(forward_demodulation,[],[f5489,f3160])).
% 4.94/0.98  fof(f5489,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f5488])).
% 4.94/0.98  fof(f5488,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67 | ~spl5_204)),
% 4.94/0.98    inference(forward_demodulation,[],[f5487,f3160])).
% 4.94/0.98  fof(f5487,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | ~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_38 | ~spl5_53 | ~spl5_67)),
% 4.94/0.98    inference(forward_demodulation,[],[f5486,f290])).
% 4.94/0.98  fof(f5486,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_3 | ~spl5_53 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f5485,f129])).
% 4.94/0.98  fof(f5485,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_2 | ~spl5_53 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f5480,f125])).
% 4.94/0.98  fof(f5480,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,X1,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(X1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(X1),k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),k1_xboole_0))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(X1) | v5_pre_topc(X0,X1,sK1)) ) | (~spl5_53 | ~spl5_67)),
% 4.94/0.98    inference(superposition,[],[f555,f388])).
% 4.94/0.98  fof(f5118,plain,(
% 4.94/0.98    ~spl5_125 | spl5_88 | ~spl5_121 | ~spl5_75 | ~spl5_158 | ~spl5_173 | ~spl5_344),
% 4.94/0.98    inference(avatar_split_clause,[],[f5104,f5091,f2217,f2077,f621,f1545,f905,f1567])).
% 4.94/0.98  fof(f1567,plain,(
% 4.94/0.98    spl5_125 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_125])])).
% 4.94/0.98  fof(f905,plain,(
% 4.94/0.98    spl5_88 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_88])])).
% 4.94/0.98  fof(f1545,plain,(
% 4.94/0.98    spl5_121 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_121])])).
% 4.94/0.98  fof(f2077,plain,(
% 4.94/0.98    spl5_158 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_158])])).
% 4.94/0.98  fof(f2217,plain,(
% 4.94/0.98    spl5_173 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_173])])).
% 4.94/0.98  fof(f5091,plain,(
% 4.94/0.98    spl5_344 <=> ! [X1,X0] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_344])])).
% 4.94/0.98  fof(f5104,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_75 | ~spl5_158 | ~spl5_173 | ~spl5_344)),
% 4.94/0.98    inference(subsumption_resolution,[],[f5103,f2078])).
% 4.94/0.98  fof(f2078,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~spl5_158),
% 4.94/0.98    inference(avatar_component_clause,[],[f2077])).
% 4.94/0.98  fof(f5103,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_75 | ~spl5_173 | ~spl5_344)),
% 4.94/0.98    inference(forward_demodulation,[],[f5099,f622])).
% 4.94/0.98  fof(f5099,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_173 | ~spl5_344)),
% 4.94/0.98    inference(resolution,[],[f5092,f2218])).
% 4.94/0.98  fof(f2218,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_173),
% 4.94/0.98    inference(avatar_component_clause,[],[f2217])).
% 4.94/0.98  fof(f5092,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | ~spl5_344),
% 4.94/0.98    inference(avatar_component_clause,[],[f5091])).
% 4.94/0.98  fof(f5093,plain,(
% 4.94/0.98    spl5_344 | ~spl5_10 | ~spl5_77 | ~spl5_331),
% 4.94/0.98    inference(avatar_split_clause,[],[f4967,f4956,f705,f156,f5091])).
% 4.94/0.98  fof(f4956,plain,(
% 4.94/0.98    spl5_331 <=> ! [X3,X2,X4] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4))))) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4)) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))))) | ~v1_funct_1(X2) | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_331])])).
% 4.94/0.98  fof(f4967,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_10 | ~spl5_77 | ~spl5_331)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4966,f157])).
% 4.94/0.98  fof(f4966,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_10 | ~spl5_77 | ~spl5_331)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4963,f157])).
% 4.94/0.98  fof(f4963,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X0,X1))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X0,X1)) | ~v2_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X0,X1))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) ) | (~spl5_77 | ~spl5_331)),
% 4.94/0.98    inference(resolution,[],[f4957,f706])).
% 4.94/0.98  fof(f4957,plain,(
% 4.94/0.98    ( ! [X4,X2,X3] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4))))) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4)) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))))) | ~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))) | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | ~spl5_331),
% 4.94/0.98    inference(avatar_component_clause,[],[f4956])).
% 4.94/0.98  fof(f4958,plain,(
% 4.94/0.98    spl5_331 | ~spl5_24 | ~spl5_231),
% 4.94/0.98    inference(avatar_split_clause,[],[f3932,f3927,f216,f4956])).
% 4.94/0.98  fof(f3927,plain,(
% 4.94/0.98    spl5_231 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_231])])).
% 4.94/0.98  fof(f3932,plain,(
% 4.94/0.98    ( ! [X4,X2,X3] : (~v1_funct_2(X2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(g1_pre_topc(X3,X4))))) | ~v5_pre_topc(X2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(X3,X4)) | ~v2_pre_topc(g1_pre_topc(X3,X4)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(X3,X4))))) | ~v1_funct_1(X2) | v5_pre_topc(X2,sK0,g1_pre_topc(X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k1_zfmisc_1(X3)))) ) | (~spl5_24 | ~spl5_231)),
% 4.94/0.98    inference(resolution,[],[f3928,f217])).
% 4.94/0.98  fof(f3928,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1)) ) | ~spl5_231),
% 4.94/0.98    inference(avatar_component_clause,[],[f3927])).
% 4.94/0.98  fof(f4623,plain,(
% 4.94/0.98    spl5_302 | ~spl5_21 | ~spl5_300),
% 4.94/0.98    inference(avatar_split_clause,[],[f4599,f4581,f203,f4621])).
% 4.94/0.98  fof(f203,plain,(
% 4.94/0.98    spl5_21 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 4.94/0.98  fof(f4581,plain,(
% 4.94/0.98    spl5_300 <=> ! [X9,X8] : v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_300])])).
% 4.94/0.98  fof(f4599,plain,(
% 4.94/0.98    ( ! [X15,X16] : (k1_xboole_0 = k2_partfun1(X15,k1_xboole_0,k1_xboole_0,X16)) ) | (~spl5_21 | ~spl5_300)),
% 4.94/0.98    inference(resolution,[],[f4582,f204])).
% 4.94/0.98  fof(f204,plain,(
% 4.94/0.98    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_21),
% 4.94/0.98    inference(avatar_component_clause,[],[f203])).
% 4.94/0.98  fof(f4582,plain,(
% 4.94/0.98    ( ! [X8,X9] : (v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9))) ) | ~spl5_300),
% 4.94/0.98    inference(avatar_component_clause,[],[f4581])).
% 4.94/0.98  fof(f4583,plain,(
% 4.94/0.98    spl5_300 | ~spl5_27 | ~spl5_297),
% 4.94/0.98    inference(avatar_split_clause,[],[f4571,f4555,f229,f4581])).
% 4.94/0.98  fof(f229,plain,(
% 4.94/0.98    spl5_27 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 4.94/0.98  fof(f4555,plain,(
% 4.94/0.98    spl5_297 <=> ! [X1,X0] : m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_297])])).
% 4.94/0.98  fof(f4571,plain,(
% 4.94/0.98    ( ! [X8,X9] : (v1_xboole_0(k2_partfun1(X8,k1_xboole_0,k1_xboole_0,X9))) ) | (~spl5_27 | ~spl5_297)),
% 4.94/0.98    inference(resolution,[],[f4556,f230])).
% 4.94/0.98  fof(f230,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl5_27),
% 4.94/0.98    inference(avatar_component_clause,[],[f229])).
% 4.94/0.98  fof(f4556,plain,(
% 4.94/0.98    ( ! [X0,X1] : (m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_297),
% 4.94/0.98    inference(avatar_component_clause,[],[f4555])).
% 4.94/0.98  fof(f4557,plain,(
% 4.94/0.98    spl5_297 | ~spl5_10 | ~spl5_77 | ~spl5_296),
% 4.94/0.98    inference(avatar_split_clause,[],[f4553,f4547,f705,f156,f4555])).
% 4.94/0.98  fof(f4547,plain,(
% 4.94/0.98    spl5_296 <=> ! [X1,X0,X2] : (m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_296])])).
% 4.94/0.98  fof(f4553,plain,(
% 4.94/0.98    ( ! [X0,X1] : (m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl5_10 | ~spl5_77 | ~spl5_296)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4550,f157])).
% 4.94/0.98  fof(f4550,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_partfun1(X0,k1_xboole_0,k1_xboole_0,X1),k1_zfmisc_1(k1_xboole_0))) ) | (~spl5_77 | ~spl5_296)),
% 4.94/0.98    inference(resolution,[],[f4548,f706])).
% 4.94/0.98  fof(f4548,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0))) ) | ~spl5_296),
% 4.94/0.98    inference(avatar_component_clause,[],[f4547])).
% 4.94/0.98  fof(f4549,plain,(
% 4.94/0.98    spl5_296 | ~spl5_38 | ~spl5_47),
% 4.94/0.98    inference(avatar_split_clause,[],[f372,f339,f289,f4547])).
% 4.94/0.98  fof(f339,plain,(
% 4.94/0.98    spl5_47 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 4.94/0.98  fof(f372,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_partfun1(X0,k1_xboole_0,X1,X2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1)) ) | (~spl5_38 | ~spl5_47)),
% 4.94/0.98    inference(superposition,[],[f340,f290])).
% 4.94/0.98  fof(f340,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_47),
% 4.94/0.98    inference(avatar_component_clause,[],[f339])).
% 4.94/0.98  fof(f4408,plain,(
% 4.94/0.98    spl5_282 | ~spl5_10 | ~spl5_44 | ~spl5_77 | ~spl5_242 | ~spl5_277),
% 4.94/0.98    inference(avatar_split_clause,[],[f4385,f4369,f4048,f705,f319,f156,f4406])).
% 4.94/0.98  fof(f319,plain,(
% 4.94/0.98    spl5_44 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 4.94/0.98  fof(f4048,plain,(
% 4.94/0.98    spl5_242 <=> ! [X11] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X11)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_242])])).
% 4.94/0.98  fof(f4369,plain,(
% 4.94/0.98    spl5_277 <=> ! [X1,X0] : v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_277])])).
% 4.94/0.98  fof(f4385,plain,(
% 4.94/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_44 | ~spl5_77 | ~spl5_242 | ~spl5_277)),
% 4.94/0.98    inference(forward_demodulation,[],[f4384,f4049])).
% 4.94/0.98  fof(f4049,plain,(
% 4.94/0.98    ( ! [X11] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X11)) ) | ~spl5_242),
% 4.94/0.98    inference(avatar_component_clause,[],[f4048])).
% 4.94/0.98  fof(f4384,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_44 | ~spl5_77 | ~spl5_277)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4383,f706])).
% 4.94/0.98  fof(f4383,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_10 | ~spl5_44 | ~spl5_277)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4382,f157])).
% 4.94/0.98  fof(f4382,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k7_relat_1(k1_xboole_0,X1),k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_44 | ~spl5_277)),
% 4.94/0.98    inference(superposition,[],[f4370,f320])).
% 4.94/0.98  fof(f320,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_44),
% 4.94/0.98    inference(avatar_component_clause,[],[f319])).
% 4.94/0.98  fof(f4370,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)) ) | ~spl5_277),
% 4.94/0.98    inference(avatar_component_clause,[],[f4369])).
% 4.94/0.98  fof(f4371,plain,(
% 4.94/0.98    spl5_277 | ~spl5_10 | ~spl5_47 | ~spl5_77 | ~spl5_259),
% 4.94/0.98    inference(avatar_split_clause,[],[f4356,f4251,f705,f339,f156,f4369])).
% 4.94/0.98  fof(f4251,plain,(
% 4.94/0.98    spl5_259 <=> ! [X1,X3,X0,X2] : (k1_xboole_0 != X0 | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | ~m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).
% 4.94/0.98  fof(f4356,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0)) ) | (~spl5_10 | ~spl5_47 | ~spl5_77 | ~spl5_259)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4355,f706])).
% 4.94/0.98  fof(f4355,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_10 | ~spl5_47 | ~spl5_259)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4354,f157])).
% 4.94/0.98  fof(f4354,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_47 | ~spl5_259)),
% 4.94/0.98    inference(trivial_inequality_removal,[],[f4351])).
% 4.94/0.98  fof(f4351,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(k2_partfun1(k1_xboole_0,X0,k1_xboole_0,X1),k1_xboole_0,X0) | k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | ~v1_funct_1(k1_xboole_0)) ) | (~spl5_47 | ~spl5_259)),
% 4.94/0.98    inference(resolution,[],[f4252,f340])).
% 4.94/0.98  fof(f4252,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3))) | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | k1_xboole_0 != X0) ) | ~spl5_259),
% 4.94/0.98    inference(avatar_component_clause,[],[f4251])).
% 4.94/0.98  fof(f4253,plain,(
% 4.94/0.98    spl5_259 | ~spl5_45 | ~spl5_256),
% 4.94/0.98    inference(avatar_split_clause,[],[f4240,f4228,f331,f4251])).
% 4.94/0.98  fof(f331,plain,(
% 4.94/0.98    spl5_45 <=> ! [X7,X8] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8))) | k1_xboole_0 = k1_relat_1(X7))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 4.94/0.98  fof(f4240,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_xboole_0 != X0 | v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | ~m1_subset_1(k2_partfun1(X0,X1,k1_xboole_0,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))) ) | (~spl5_45 | ~spl5_256)),
% 4.94/0.98    inference(superposition,[],[f4229,f332])).
% 4.94/0.98  fof(f332,plain,(
% 4.94/0.98    ( ! [X8,X7] : (k1_xboole_0 = k1_relat_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8)))) ) | ~spl5_45),
% 4.94/0.98    inference(avatar_component_clause,[],[f331])).
% 4.94/0.98  fof(f4230,plain,(
% 4.94/0.98    spl5_256 | ~spl5_10 | ~spl5_77 | ~spl5_254),
% 4.94/0.98    inference(avatar_split_clause,[],[f4226,f4216,f705,f156,f4228])).
% 4.94/0.98  fof(f4216,plain,(
% 4.94/0.98    spl5_254 <=> ! [X1,X3,X0,X2] : (k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_254])])).
% 4.94/0.98  fof(f4226,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0) ) | (~spl5_10 | ~spl5_77 | ~spl5_254)),
% 4.94/0.98    inference(subsumption_resolution,[],[f4223,f157])).
% 4.94/0.98  fof(f4223,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_partfun1(X0,X1,k1_xboole_0,X2),X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(k2_partfun1(X0,X1,k1_xboole_0,X2)) != X0) ) | (~spl5_77 | ~spl5_254)),
% 4.94/0.98    inference(resolution,[],[f4217,f706])).
% 4.94/0.98  fof(f4217,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0) ) | ~spl5_254),
% 4.94/0.98    inference(avatar_component_clause,[],[f4216])).
% 4.94/0.98  fof(f4218,plain,(
% 4.94/0.98    spl5_254 | ~spl5_34 | ~spl5_47 | ~spl5_142),
% 4.94/0.98    inference(avatar_split_clause,[],[f1684,f1676,f339,f263,f4216])).
% 4.94/0.98  fof(f1676,plain,(
% 4.94/0.98    spl5_142 <=> ! [X1,X3,X0,X2] : (k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 4.94/0.98  fof(f1684,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl5_34 | ~spl5_47 | ~spl5_142)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1682,f340])).
% 4.94/0.98  fof(f1682,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_relat_1(k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_34 | ~spl5_142)),
% 4.94/0.98    inference(superposition,[],[f1677,f264])).
% 4.94/0.98  fof(f1677,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_142),
% 4.94/0.98    inference(avatar_component_clause,[],[f1676])).
% 4.94/0.98  fof(f4050,plain,(
% 4.94/0.98    spl5_242 | ~spl5_21 | ~spl5_237),
% 4.94/0.98    inference(avatar_split_clause,[],[f4000,f3980,f203,f4048])).
% 4.94/0.98  fof(f3980,plain,(
% 4.94/0.98    spl5_237 <=> ! [X0] : v1_xboole_0(k7_relat_1(k1_xboole_0,X0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_237])])).
% 4.94/0.98  fof(f4000,plain,(
% 4.94/0.98    ( ! [X11] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X11)) ) | (~spl5_21 | ~spl5_237)),
% 4.94/0.98    inference(resolution,[],[f3981,f204])).
% 4.94/0.98  fof(f3981,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | ~spl5_237),
% 4.94/0.98    inference(avatar_component_clause,[],[f3980])).
% 4.94/0.98  fof(f3982,plain,(
% 4.94/0.98    spl5_237 | ~spl5_10 | ~spl5_77 | ~spl5_235),
% 4.94/0.98    inference(avatar_split_clause,[],[f3974,f3961,f705,f156,f3980])).
% 4.94/0.98  fof(f3961,plain,(
% 4.94/0.98    spl5_235 <=> ! [X3,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2) | v1_xboole_0(k7_relat_1(X2,X3)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_235])])).
% 4.94/0.98  fof(f3974,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | (~spl5_10 | ~spl5_77 | ~spl5_235)),
% 4.94/0.98    inference(subsumption_resolution,[],[f3971,f157])).
% 4.94/0.98  fof(f3971,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k7_relat_1(k1_xboole_0,X0))) ) | (~spl5_77 | ~spl5_235)),
% 4.94/0.98    inference(resolution,[],[f3962,f706])).
% 4.94/0.98  fof(f3962,plain,(
% 4.94/0.98    ( ! [X2,X3] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k7_relat_1(X2,X3))) ) | ~spl5_235),
% 4.94/0.98    inference(avatar_component_clause,[],[f3961])).
% 4.94/0.98  fof(f3963,plain,(
% 4.94/0.98    spl5_235 | ~spl5_27 | ~spl5_232),
% 4.94/0.98    inference(avatar_split_clause,[],[f3947,f3939,f229,f3961])).
% 4.94/0.98  fof(f3939,plain,(
% 4.94/0.98    spl5_232 <=> ! [X1,X2] : (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_232])])).
% 4.94/0.98  fof(f3947,plain,(
% 4.94/0.98    ( ! [X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X2) | v1_xboole_0(k7_relat_1(X2,X3))) ) | (~spl5_27 | ~spl5_232)),
% 4.94/0.98    inference(resolution,[],[f3940,f230])).
% 4.94/0.98  fof(f3940,plain,(
% 4.94/0.98    ( ! [X2,X1] : (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1)) ) | ~spl5_232),
% 4.94/0.98    inference(avatar_component_clause,[],[f3939])).
% 4.94/0.98  fof(f3941,plain,(
% 4.94/0.98    spl5_232 | ~spl5_38 | ~spl5_97),
% 4.94/0.98    inference(avatar_split_clause,[],[f1022,f1018,f289,f3939])).
% 4.94/0.98  fof(f1018,plain,(
% 4.94/0.98    spl5_97 <=> ! [X1,X3,X0,X2] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 4.94/0.98  fof(f1022,plain,(
% 4.94/0.98    ( ! [X2,X1] : (m1_subset_1(k7_relat_1(X1,X2),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X1)) ) | (~spl5_38 | ~spl5_97)),
% 4.94/0.98    inference(superposition,[],[f1019,f290])).
% 4.94/0.98  fof(f1019,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_97),
% 4.94/0.98    inference(avatar_component_clause,[],[f1018])).
% 4.94/0.98  fof(f3929,plain,(
% 4.94/0.98    spl5_231 | ~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94),
% 4.94/0.98    inference(avatar_split_clause,[],[f3433,f995,f857,f614,f433,f391,f136,f132,f3927])).
% 4.94/0.98  fof(f433,plain,(
% 4.94/0.98    spl5_58 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 4.94/0.98  fof(f995,plain,(
% 4.94/0.98    spl5_94 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 4.94/0.98  fof(f3433,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94)),
% 4.94/0.98    inference(forward_demodulation,[],[f3432,f858])).
% 4.94/0.98  fof(f3432,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94)),
% 4.94/0.98    inference(forward_demodulation,[],[f3431,f615])).
% 4.94/0.98  fof(f3431,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94)),
% 4.94/0.98    inference(forward_demodulation,[],[f3430,f858])).
% 4.94/0.98  fof(f3430,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94)),
% 4.94/0.98    inference(forward_demodulation,[],[f3429,f615])).
% 4.94/0.98  fof(f3429,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83 | ~spl5_94)),
% 4.94/0.98    inference(subsumption_resolution,[],[f3428,f996])).
% 4.94/0.98  fof(f996,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | ~spl5_94),
% 4.94/0.98    inference(avatar_component_clause,[],[f995])).
% 4.94/0.98  fof(f3428,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83)),
% 4.94/0.98    inference(forward_demodulation,[],[f3427,f858])).
% 4.94/0.98  fof(f3427,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83)),
% 4.94/0.98    inference(forward_demodulation,[],[f3426,f615])).
% 4.94/0.98  fof(f3426,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,k1_xboole_0,u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83)),
% 4.94/0.98    inference(forward_demodulation,[],[f3425,f858])).
% 4.94/0.98  fof(f3425,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(k1_xboole_0),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83)),
% 4.94/0.98    inference(forward_demodulation,[],[f3424,f615])).
% 4.94/0.98  fof(f3424,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73 | ~spl5_83)),
% 4.94/0.98    inference(forward_demodulation,[],[f3423,f858])).
% 4.94/0.98  fof(f3423,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58 | ~spl5_73)),
% 4.94/0.98    inference(forward_demodulation,[],[f568,f615])).
% 4.94/0.98  fof(f568,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_54 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f567,f133])).
% 4.94/0.98  fof(f567,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_5 | ~spl5_54 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f566,f137])).
% 4.94/0.98  fof(f566,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_54 | ~spl5_58)),
% 4.94/0.98    inference(superposition,[],[f392,f434])).
% 4.94/0.98  fof(f434,plain,(
% 4.94/0.98    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl5_58),
% 4.94/0.98    inference(avatar_component_clause,[],[f433])).
% 4.94/0.98  fof(f3617,plain,(
% 4.94/0.98    ~spl5_197 | ~spl5_24 | spl5_210),
% 4.94/0.98    inference(avatar_split_clause,[],[f3612,f3608,f216,f2761])).
% 4.94/0.98  fof(f2761,plain,(
% 4.94/0.98    spl5_197 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_197])])).
% 4.94/0.98  fof(f3612,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl5_24 | spl5_210)),
% 4.94/0.98    inference(resolution,[],[f3609,f217])).
% 4.94/0.98  fof(f3609,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl5_210),
% 4.94/0.98    inference(avatar_component_clause,[],[f3608])).
% 4.94/0.98  fof(f2763,plain,(
% 4.94/0.98    spl5_197 | ~spl5_3 | ~spl5_22 | ~spl5_53),
% 4.94/0.98    inference(avatar_split_clause,[],[f2698,f387,f207,f128,f2761])).
% 4.94/0.98  fof(f2698,plain,(
% 4.94/0.98    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | (~spl5_3 | ~spl5_22 | ~spl5_53)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2687,f129])).
% 4.94/0.98  fof(f2687,plain,(
% 4.94/0.98    m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(k1_xboole_0))) | ~l1_pre_topc(sK1) | (~spl5_22 | ~spl5_53)),
% 4.94/0.98    inference(superposition,[],[f208,f388])).
% 4.94/0.98  fof(f2722,plain,(
% 4.94/0.98    spl5_193 | ~spl5_2 | ~spl5_3 | ~spl5_29 | ~spl5_53),
% 4.94/0.98    inference(avatar_split_clause,[],[f2695,f387,f237,f128,f124,f2720])).
% 4.94/0.98  fof(f2695,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_29 | ~spl5_53)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2694,f125])).
% 4.94/0.98  fof(f2694,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | (~spl5_3 | ~spl5_29 | ~spl5_53)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2685,f129])).
% 4.94/0.98  fof(f2685,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl5_29 | ~spl5_53)),
% 4.94/0.98    inference(superposition,[],[f238,f388])).
% 4.94/0.98  fof(f2493,plain,(
% 4.94/0.98    spl5_88 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_75 | ~spl5_77 | ~spl5_82 | ~spl5_85 | ~spl5_93 | ~spl5_98),
% 4.94/0.98    inference(avatar_split_clause,[],[f2492,f1024,f991,f874,f840,f705,f621,f559,f156,f136,f132,f128,f124,f905])).
% 4.94/0.98  fof(f874,plain,(
% 4.94/0.98    spl5_85 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_85])])).
% 4.94/0.98  fof(f991,plain,(
% 4.94/0.98    spl5_93 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 4.94/0.98  fof(f1024,plain,(
% 4.94/0.98    spl5_98 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 4.94/0.98  fof(f2492,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_75 | ~spl5_77 | ~spl5_82 | ~spl5_85 | ~spl5_93 | ~spl5_98)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2491,f992])).
% 4.94/0.98  fof(f992,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_93),
% 4.94/0.98    inference(avatar_component_clause,[],[f991])).
% 4.94/0.98  fof(f2491,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_75 | ~spl5_77 | ~spl5_82 | ~spl5_85 | ~spl5_98)),
% 4.94/0.98    inference(forward_demodulation,[],[f2490,f875])).
% 4.94/0.98  fof(f875,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(sK0) | ~spl5_85),
% 4.94/0.98    inference(avatar_component_clause,[],[f874])).
% 4.94/0.98  fof(f2490,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_75 | ~spl5_77 | ~spl5_82 | ~spl5_85 | ~spl5_98)),
% 4.94/0.98    inference(forward_demodulation,[],[f2489,f622])).
% 4.94/0.98  fof(f2489,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_85 | ~spl5_98)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2488,f1025])).
% 4.94/0.98  fof(f1025,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~spl5_98),
% 4.94/0.98    inference(avatar_component_clause,[],[f1024])).
% 4.94/0.98  fof(f2488,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82 | ~spl5_85)),
% 4.94/0.98    inference(forward_demodulation,[],[f2487,f875])).
% 4.94/0.98  fof(f2487,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2486,f133])).
% 4.94/0.98  fof(f2486,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2485,f157])).
% 4.94/0.98  fof(f2485,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2484,f157])).
% 4.94/0.98  fof(f2484,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_68 | ~spl5_77 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2483,f706])).
% 4.94/0.98  fof(f2483,plain,(
% 4.94/0.98    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2482,f129])).
% 4.94/0.98  fof(f2482,plain,(
% 4.94/0.98    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2481,f125])).
% 4.94/0.98  fof(f2481,plain,(
% 4.94/0.98    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_68 | ~spl5_82)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2464,f137])).
% 4.94/0.98  fof(f2464,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_68 | ~spl5_82)),
% 4.94/0.98    inference(resolution,[],[f841,f560])).
% 4.94/0.98  fof(f2480,plain,(
% 4.94/0.98    ~spl5_120 | ~spl5_121 | ~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | spl5_15 | ~spl5_55 | ~spl5_73 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107 | ~spl5_158),
% 4.94/0.98    inference(avatar_split_clause,[],[f2432,f2077,f1297,f905,f874,f857,f836,f705,f621,f614,f395,f175,f156,f140,f136,f132,f1545,f1542])).
% 4.94/0.98  fof(f1542,plain,(
% 4.94/0.98    spl5_120 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_120])])).
% 4.94/0.98  fof(f2432,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | spl5_15 | ~spl5_55 | ~spl5_73 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107 | ~spl5_158)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2399,f2420])).
% 4.94/0.98  fof(f2420,plain,(
% 4.94/0.98    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl5_15 | ~spl5_73 | ~spl5_85)),
% 4.94/0.98    inference(forward_demodulation,[],[f2419,f615])).
% 4.94/0.98  fof(f2419,plain,(
% 4.94/0.98    ~v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl5_15 | ~spl5_85)),
% 4.94/0.98    inference(forward_demodulation,[],[f176,f875])).
% 4.94/0.98  fof(f2399,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107 | ~spl5_158)),
% 4.94/0.98    inference(forward_demodulation,[],[f2398,f875])).
% 4.94/0.98  fof(f2398,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107 | ~spl5_158)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2397,f2078])).
% 4.94/0.98  fof(f2397,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f2396,f875])).
% 4.94/0.98  fof(f2396,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f2395,f622])).
% 4.94/0.98  fof(f2395,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_6 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_81 | ~spl5_83 | ~spl5_85 | ~spl5_88 | ~spl5_107)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2388,f2394])).
% 4.94/0.98  fof(f2394,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_6 | ~spl5_75 | ~spl5_81 | ~spl5_83 | ~spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f1919,f858])).
% 4.94/0.98  fof(f1919,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl5_6 | ~spl5_75 | ~spl5_81 | ~spl5_107)),
% 4.94/0.98    inference(backward_demodulation,[],[f1812,f622])).
% 4.94/0.98  fof(f1812,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_6 | ~spl5_81 | ~spl5_107)),
% 4.94/0.98    inference(backward_demodulation,[],[f1298,f1792])).
% 4.94/0.98  fof(f1792,plain,(
% 4.94/0.98    k1_xboole_0 = sK2 | (~spl5_6 | ~spl5_81)),
% 4.94/0.98    inference(backward_demodulation,[],[f141,f837])).
% 4.94/0.98  fof(f1298,plain,(
% 4.94/0.98    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_107),
% 4.94/0.98    inference(avatar_component_clause,[],[f1297])).
% 4.94/0.98  fof(f2388,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_85 | ~spl5_88)),
% 4.94/0.98    inference(forward_demodulation,[],[f2387,f875])).
% 4.94/0.98  fof(f2387,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_75 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(forward_demodulation,[],[f2386,f622])).
% 4.94/0.98  fof(f2386,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2385,f133])).
% 4.94/0.98  fof(f2385,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2384,f157])).
% 4.94/0.98  fof(f2384,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_10 | ~spl5_55 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2383,f157])).
% 4.94/0.98  fof(f2383,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2382,f706])).
% 4.94/0.98  fof(f2382,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_55 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2356,f137])).
% 4.94/0.98  fof(f2356,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK0) | (~spl5_55 | ~spl5_88)),
% 4.94/0.98    inference(resolution,[],[f906,f396])).
% 4.94/0.98  fof(f906,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_88),
% 4.94/0.98    inference(avatar_component_clause,[],[f905])).
% 4.94/0.98  fof(f2433,plain,(
% 4.94/0.98    spl5_93 | ~spl5_6 | ~spl5_75 | ~spl5_81 | ~spl5_83 | ~spl5_107),
% 4.94/0.98    inference(avatar_split_clause,[],[f2394,f1297,f857,f836,f621,f140,f991])).
% 4.94/0.98  fof(f2370,plain,(
% 4.94/0.98    ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_75 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88 | ~spl5_93 | ~spl5_98),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f2369])).
% 4.94/0.98  fof(f2369,plain,(
% 4.94/0.98    $false | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_75 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88 | ~spl5_93 | ~spl5_98)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2368,f992])).
% 4.94/0.98  fof(f2368,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_75 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88 | ~spl5_98)),
% 4.94/0.98    inference(forward_demodulation,[],[f2367,f875])).
% 4.94/0.98  fof(f2367,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_75 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88 | ~spl5_98)),
% 4.94/0.98    inference(forward_demodulation,[],[f2366,f622])).
% 4.94/0.98  fof(f2366,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88 | ~spl5_98)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2365,f1025])).
% 4.94/0.98  fof(f2365,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | spl5_82 | ~spl5_85 | ~spl5_88)),
% 4.94/0.98    inference(forward_demodulation,[],[f2364,f875])).
% 4.94/0.98  fof(f2364,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | spl5_82 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2363,f2074])).
% 4.94/0.98  fof(f2363,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2362,f133])).
% 4.94/0.98  fof(f2362,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2361,f157])).
% 4.94/0.98  fof(f2361,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_10 | ~spl5_67 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2360,f157])).
% 4.94/0.98  fof(f2360,plain,(
% 4.94/0.98    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_67 | ~spl5_77 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2359,f706])).
% 4.94/0.98  fof(f2359,plain,(
% 4.94/0.98    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_67 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2358,f129])).
% 4.94/0.98  fof(f2358,plain,(
% 4.94/0.98    ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_2 | ~spl5_5 | ~spl5_67 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2357,f125])).
% 4.94/0.98  fof(f2357,plain,(
% 4.94/0.98    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_5 | ~spl5_67 | ~spl5_88)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2354,f137])).
% 4.94/0.98  fof(f2354,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(sK0) | v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_67 | ~spl5_88)),
% 4.94/0.98    inference(resolution,[],[f906,f555])).
% 4.94/0.98  fof(f2219,plain,(
% 4.94/0.98    spl5_173 | ~spl5_6 | ~spl5_10 | ~spl5_45 | ~spl5_62 | ~spl5_81),
% 4.94/0.98    inference(avatar_split_clause,[],[f2017,f836,f528,f331,f156,f140,f2217])).
% 4.94/0.98  fof(f528,plain,(
% 4.94/0.98    spl5_62 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 4.94/0.98  fof(f2017,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_6 | ~spl5_10 | ~spl5_45 | ~spl5_62 | ~spl5_81)),
% 4.94/0.98    inference(subsumption_resolution,[],[f2016,f157])).
% 4.94/0.98  fof(f2016,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ) | (~spl5_6 | ~spl5_45 | ~spl5_62 | ~spl5_81)),
% 4.94/0.98    inference(forward_demodulation,[],[f1939,f1792])).
% 4.94/0.98  fof(f1939,plain,(
% 4.94/0.98    ( ! [X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_6 | ~spl5_45 | ~spl5_62 | ~spl5_81)),
% 4.94/0.98    inference(forward_demodulation,[],[f1523,f1792])).
% 4.94/0.98  fof(f1523,plain,(
% 4.94/0.98    ( ! [X0] : (v5_pre_topc(sK2,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_45 | ~spl5_62)),
% 4.94/0.98    inference(superposition,[],[f1518,f332])).
% 4.94/0.98  fof(f1518,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl5_62),
% 4.94/0.98    inference(avatar_component_clause,[],[f528])).
% 4.94/0.98  fof(f2079,plain,(
% 4.94/0.98    spl5_158 | ~spl5_6 | ~spl5_75 | ~spl5_81 | ~spl5_103),
% 4.94/0.98    inference(avatar_split_clause,[],[f1977,f1132,f836,f621,f140,f2077])).
% 4.94/0.98  fof(f1132,plain,(
% 4.94/0.98    spl5_103 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_103])])).
% 4.94/0.98  fof(f1977,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl5_6 | ~spl5_75 | ~spl5_81 | ~spl5_103)),
% 4.94/0.98    inference(forward_demodulation,[],[f1976,f1792])).
% 4.94/0.98  fof(f1976,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl5_75 | ~spl5_103)),
% 4.94/0.98    inference(forward_demodulation,[],[f1133,f622])).
% 4.94/0.98  fof(f1133,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_103),
% 4.94/0.98    inference(avatar_component_clause,[],[f1132])).
% 4.94/0.98  fof(f2075,plain,(
% 4.94/0.98    ~spl5_82 | ~spl5_6 | spl5_14 | ~spl5_81),
% 4.94/0.98    inference(avatar_split_clause,[],[f1794,f836,f172,f140,f840])).
% 4.94/0.98  fof(f172,plain,(
% 4.94/0.98    spl5_14 <=> v5_pre_topc(sK2,sK0,sK1)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 4.94/0.98  fof(f1794,plain,(
% 4.94/0.98    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_6 | spl5_14 | ~spl5_81)),
% 4.94/0.98    inference(backward_demodulation,[],[f173,f1792])).
% 4.94/0.98  fof(f173,plain,(
% 4.94/0.98    ~v5_pre_topc(sK2,sK0,sK1) | spl5_14),
% 4.94/0.98    inference(avatar_component_clause,[],[f172])).
% 4.94/0.98  fof(f1938,plain,(
% 4.94/0.98    ~spl5_6 | ~spl5_10 | ~spl5_45 | spl5_74 | ~spl5_81),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f1937])).
% 4.94/0.98  fof(f1937,plain,(
% 4.94/0.98    $false | (~spl5_6 | ~spl5_10 | ~spl5_45 | spl5_74 | ~spl5_81)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1936,f157])).
% 4.94/0.98  fof(f1936,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_6 | ~spl5_45 | spl5_74 | ~spl5_81)),
% 4.94/0.98    inference(forward_demodulation,[],[f1461,f1792])).
% 4.94/0.98  fof(f1461,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_45 | spl5_74)),
% 4.94/0.98    inference(trivial_inequality_removal,[],[f1460])).
% 4.94/0.98  fof(f1460,plain,(
% 4.94/0.98    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_45 | spl5_74)),
% 4.94/0.98    inference(superposition,[],[f1457,f332])).
% 4.94/0.98  fof(f1457,plain,(
% 4.94/0.98    k1_xboole_0 != k1_relat_1(sK2) | spl5_74),
% 4.94/0.98    inference(avatar_component_clause,[],[f617])).
% 4.94/0.98  fof(f617,plain,(
% 4.94/0.98    spl5_74 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 4.94/0.98  fof(f1780,plain,(
% 4.94/0.98    spl5_110 | ~spl5_119 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106 | ~spl5_107 | ~spl5_108),
% 4.94/0.98    inference(avatar_split_clause,[],[f1779,f1313,f1297,f1293,f554,f528,f473,f428,f422,f128,f124,f120,f1473,f1328])).
% 4.94/0.98  fof(f1328,plain,(
% 4.94/0.98    spl5_110 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 4.94/0.98  fof(f1473,plain,(
% 4.94/0.98    spl5_119 <=> l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_119])])).
% 4.94/0.98  fof(f120,plain,(
% 4.94/0.98    spl5_1 <=> v1_funct_1(sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 4.94/0.98  fof(f422,plain,(
% 4.94/0.98    spl5_56 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 4.94/0.98  fof(f428,plain,(
% 4.94/0.98    spl5_57 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 4.94/0.98  fof(f473,plain,(
% 4.94/0.98    spl5_60 <=> v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 4.94/0.98  fof(f1293,plain,(
% 4.94/0.98    spl5_106 <=> k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_106])])).
% 4.94/0.98  fof(f1313,plain,(
% 4.94/0.98    spl5_108 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_108])])).
% 4.94/0.98  fof(f1779,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106 | ~spl5_107 | ~spl5_108)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1778,f1314])).
% 4.94/0.98  fof(f1314,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_108),
% 4.94/0.98    inference(avatar_component_clause,[],[f1313])).
% 4.94/0.98  fof(f1778,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106 | ~spl5_107)),
% 4.94/0.98    inference(forward_demodulation,[],[f1777,f1294])).
% 4.94/0.98  fof(f1294,plain,(
% 4.94/0.98    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl5_106),
% 4.94/0.98    inference(avatar_component_clause,[],[f1293])).
% 4.94/0.98  fof(f1777,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106 | ~spl5_107)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1776,f1298])).
% 4.94/0.98  fof(f1776,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106)),
% 4.94/0.98    inference(forward_demodulation,[],[f1775,f1294])).
% 4.94/0.98  fof(f1775,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1774,f429])).
% 4.94/0.98  fof(f429,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl5_57),
% 4.94/0.98    inference(avatar_component_clause,[],[f428])).
% 4.94/0.98  fof(f1774,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106)),
% 4.94/0.98    inference(forward_demodulation,[],[f1773,f1294])).
% 4.94/0.98  fof(f1773,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1772,f423])).
% 4.94/0.98  fof(f423,plain,(
% 4.94/0.98    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl5_56),
% 4.94/0.98    inference(avatar_component_clause,[],[f422])).
% 4.94/0.98  fof(f1772,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_60 | ~spl5_62 | ~spl5_67 | ~spl5_106)),
% 4.94/0.98    inference(forward_demodulation,[],[f1771,f1294])).
% 4.94/0.98  fof(f1771,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_60 | ~spl5_62 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1770,f474])).
% 4.94/0.98  fof(f474,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~spl5_60),
% 4.94/0.98    inference(avatar_component_clause,[],[f473])).
% 4.94/0.98  fof(f1770,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_62 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1769,f121])).
% 4.94/0.98  fof(f121,plain,(
% 4.94/0.98    v1_funct_1(sK2) | ~spl5_1),
% 4.94/0.98    inference(avatar_component_clause,[],[f120])).
% 4.94/0.98  fof(f1769,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_3 | ~spl5_62 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1768,f129])).
% 4.94/0.98  fof(f1768,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_2 | ~spl5_62 | ~spl5_67)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1520,f125])).
% 4.94/0.98  fof(f1520,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_62 | ~spl5_67)),
% 4.94/0.98    inference(resolution,[],[f1518,f555])).
% 4.94/0.98  fof(f1763,plain,(
% 4.94/0.98    ~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_14 | ~spl5_56 | ~spl5_57 | ~spl5_110 | ~spl5_157),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f1759])).
% 4.94/0.98  fof(f1759,plain,(
% 4.94/0.98    $false | (~spl5_1 | ~spl5_2 | ~spl5_3 | spl5_14 | ~spl5_56 | ~spl5_57 | ~spl5_110 | ~spl5_157)),
% 4.94/0.98    inference(unit_resulting_resolution,[],[f125,f121,f129,f173,f423,f429,f1329,f1757])).
% 4.94/0.98  fof(f1757,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1)) ) | ~spl5_157),
% 4.94/0.98    inference(avatar_component_clause,[],[f1756])).
% 4.94/0.98  fof(f1756,plain,(
% 4.94/0.98    spl5_157 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_157])])).
% 4.94/0.98  fof(f1329,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~spl5_110),
% 4.94/0.98    inference(avatar_component_clause,[],[f1328])).
% 4.94/0.98  fof(f1758,plain,(
% 4.94/0.98    spl5_157 | ~spl5_4 | ~spl5_5 | ~spl5_34 | ~spl5_54 | ~spl5_58 | ~spl5_65 | ~spl5_76),
% 4.94/0.98    inference(avatar_split_clause,[],[f1278,f624,f545,f433,f391,f263,f136,f132,f1756])).
% 4.94/0.98  fof(f545,plain,(
% 4.94/0.98    spl5_65 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 4.94/0.98  fof(f624,plain,(
% 4.94/0.98    spl5_76 <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_76])])).
% 4.94/0.98  fof(f1278,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_34 | ~spl5_54 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f1277])).
% 4.94/0.98  fof(f1277,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_34 | ~spl5_54 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(forward_demodulation,[],[f1276,f1264])).
% 4.94/0.98  fof(f1264,plain,(
% 4.94/0.98    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_34 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1257,f546])).
% 4.94/0.98  fof(f546,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl5_65),
% 4.94/0.98    inference(avatar_component_clause,[],[f545])).
% 4.94/0.98  fof(f1257,plain,(
% 4.94/0.98    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_34 | ~spl5_76)),
% 4.94/0.98    inference(superposition,[],[f625,f264])).
% 4.94/0.98  fof(f625,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl5_76),
% 4.94/0.98    inference(avatar_component_clause,[],[f624])).
% 4.94/0.98  fof(f1276,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_34 | ~spl5_54 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f1267])).
% 4.94/0.98  fof(f1267,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_34 | ~spl5_54 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(backward_demodulation,[],[f568,f1264])).
% 4.94/0.98  fof(f1678,plain,(
% 4.94/0.98    spl5_142 | ~spl5_47 | ~spl5_100),
% 4.94/0.98    inference(avatar_split_clause,[],[f1428,f1042,f339,f1676])).
% 4.94/0.98  fof(f1042,plain,(
% 4.94/0.98    spl5_100 <=> ! [X3,X5,X7,X2,X4,X6] : (~m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6 | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_100])])).
% 4.94/0.98  fof(f1428,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl5_47 | ~spl5_100)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f1424])).
% 4.94/0.98  fof(f1424,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (k1_relset_1(X0,X1,k2_partfun1(X0,X1,X2,X3)) != X0 | v1_funct_2(k2_partfun1(X0,X1,X2,X3),X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl5_47 | ~spl5_100)),
% 4.94/0.98    inference(resolution,[],[f1043,f340])).
% 4.94/0.98  fof(f1043,plain,(
% 4.94/0.98    ( ! [X6,X4,X2,X7,X5,X3] : (~m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6 | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | ~spl5_100),
% 4.94/0.98    inference(avatar_component_clause,[],[f1042])).
% 4.94/0.98  fof(f1602,plain,(
% 4.94/0.98    spl5_62 | ~spl5_119 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_107 | ~spl5_108 | ~spl5_110),
% 4.94/0.98    inference(avatar_split_clause,[],[f1514,f1328,f1313,f1297,f1293,f559,f473,f428,f422,f128,f124,f120,f1473,f528])).
% 4.94/0.98  fof(f1514,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_107 | ~spl5_108 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1513,f1314])).
% 4.94/0.98  fof(f1513,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_107 | ~spl5_110)),
% 4.94/0.98    inference(forward_demodulation,[],[f1512,f1294])).
% 4.94/0.98  fof(f1512,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_107 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1511,f1298])).
% 4.94/0.98  fof(f1511,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_110)),
% 4.94/0.98    inference(forward_demodulation,[],[f1510,f1294])).
% 4.94/0.98  fof(f1510,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_57 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1509,f429])).
% 4.94/0.98  fof(f1509,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_110)),
% 4.94/0.98    inference(forward_demodulation,[],[f1508,f1294])).
% 4.94/0.98  fof(f1508,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_56 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1507,f423])).
% 4.94/0.98  fof(f1507,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_60 | ~spl5_68 | ~spl5_106 | ~spl5_110)),
% 4.94/0.98    inference(forward_demodulation,[],[f1506,f1294])).
% 4.94/0.98  fof(f1506,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_60 | ~spl5_68 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1336,f474])).
% 4.94/0.98  fof(f1336,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_68 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1335,f121])).
% 4.94/0.98  fof(f1335,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_3 | ~spl5_68 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1334,f129])).
% 4.94/0.98  fof(f1334,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_2 | ~spl5_68 | ~spl5_110)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1331,f125])).
% 4.94/0.98  fof(f1331,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_68 | ~spl5_110)),
% 4.94/0.98    inference(resolution,[],[f1329,f560])).
% 4.94/0.98  fof(f1575,plain,(
% 4.94/0.98    ~spl5_3 | ~spl5_22 | spl5_125),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f1574])).
% 4.94/0.98  fof(f1574,plain,(
% 4.94/0.98    $false | (~spl5_3 | ~spl5_22 | spl5_125)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1572,f129])).
% 4.94/0.98  fof(f1572,plain,(
% 4.94/0.98    ~l1_pre_topc(sK1) | (~spl5_22 | spl5_125)),
% 4.94/0.98    inference(resolution,[],[f1568,f208])).
% 4.94/0.98  fof(f1568,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl5_125),
% 4.94/0.98    inference(avatar_component_clause,[],[f1567])).
% 4.94/0.98  fof(f1569,plain,(
% 4.94/0.98    ~spl5_125 | ~spl5_24 | spl5_120),
% 4.94/0.98    inference(avatar_split_clause,[],[f1557,f1542,f216,f1567])).
% 4.94/0.98  fof(f1557,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | (~spl5_24 | spl5_120)),
% 4.94/0.98    inference(resolution,[],[f1543,f217])).
% 4.94/0.98  fof(f1543,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_120),
% 4.94/0.98    inference(avatar_component_clause,[],[f1542])).
% 4.94/0.98  fof(f1563,plain,(
% 4.94/0.98    ~spl5_2 | ~spl5_3 | ~spl5_29 | spl5_121),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f1562])).
% 4.94/0.98  fof(f1562,plain,(
% 4.94/0.98    $false | (~spl5_2 | ~spl5_3 | ~spl5_29 | spl5_121)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1561,f125])).
% 4.94/0.98  fof(f1561,plain,(
% 4.94/0.98    ~v2_pre_topc(sK1) | (~spl5_3 | ~spl5_29 | spl5_121)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1559,f129])).
% 4.94/0.98  fof(f1559,plain,(
% 4.94/0.98    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl5_29 | spl5_121)),
% 4.94/0.98    inference(resolution,[],[f1546,f238])).
% 4.94/0.98  fof(f1546,plain,(
% 4.94/0.98    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl5_121),
% 4.94/0.98    inference(avatar_component_clause,[],[f1545])).
% 4.94/0.98  fof(f1519,plain,(
% 4.94/0.98    spl5_62 | ~spl5_15 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f1515,f433,f175,f528])).
% 4.94/0.98  fof(f1515,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_15 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f179,f434])).
% 4.94/0.98  fof(f1481,plain,(
% 4.94/0.98    ~spl5_24 | ~spl5_66 | spl5_119),
% 4.94/0.98    inference(avatar_contradiction_clause,[],[f1480])).
% 4.94/0.98  fof(f1480,plain,(
% 4.94/0.98    $false | (~spl5_24 | ~spl5_66 | spl5_119)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1477,f550])).
% 4.94/0.98  fof(f550,plain,(
% 4.94/0.98    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~spl5_66),
% 4.94/0.98    inference(avatar_component_clause,[],[f549])).
% 4.94/0.98  fof(f549,plain,(
% 4.94/0.98    spl5_66 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 4.94/0.98  fof(f1477,plain,(
% 4.94/0.98    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl5_24 | spl5_119)),
% 4.94/0.98    inference(resolution,[],[f1474,f217])).
% 4.94/0.98  fof(f1474,plain,(
% 4.94/0.98    ~l1_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | spl5_119),
% 4.94/0.98    inference(avatar_component_clause,[],[f1473])).
% 4.94/0.98  fof(f1330,plain,(
% 4.94/0.98    spl5_110 | ~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_34 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58 | ~spl5_65 | ~spl5_76),
% 4.94/0.98    inference(avatar_split_clause,[],[f1281,f624,f545,f433,f428,f422,f395,f263,f172,f136,f132,f128,f124,f120,f1328])).
% 4.94/0.98  fof(f1281,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_34 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1280,f429])).
% 4.94/0.98  fof(f1280,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_34 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(forward_demodulation,[],[f1279,f1264])).
% 4.94/0.98  fof(f1279,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_34 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(subsumption_resolution,[],[f1268,f423])).
% 4.94/0.98  fof(f1268,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_34 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(backward_demodulation,[],[f581,f1264])).
% 4.94/0.98  fof(f581,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f580,f434])).
% 4.94/0.98  fof(f580,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f579,f434])).
% 4.94/0.98  fof(f579,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f578,f434])).
% 4.94/0.98  fof(f578,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_57 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f577,f429])).
% 4.94/0.98  fof(f577,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f576,f434])).
% 4.94/0.98  fof(f576,plain,(
% 4.94/0.98    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_56 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f575,f423])).
% 4.94/0.98  fof(f575,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55 | ~spl5_58)),
% 4.94/0.98    inference(forward_demodulation,[],[f574,f434])).
% 4.94/0.98  fof(f574,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(subsumption_resolution,[],[f573,f133])).
% 4.94/0.98  fof(f573,plain,(
% 4.94/0.98    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(subsumption_resolution,[],[f572,f121])).
% 4.94/0.98  fof(f572,plain,(
% 4.94/0.98    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_5 | ~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(subsumption_resolution,[],[f571,f129])).
% 4.94/0.98  fof(f571,plain,(
% 4.94/0.98    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_2 | ~spl5_5 | ~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(subsumption_resolution,[],[f570,f125])).
% 4.94/0.98  fof(f570,plain,(
% 4.94/0.98    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(subsumption_resolution,[],[f569,f137])).
% 4.94/0.98  fof(f569,plain,(
% 4.94/0.98    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)))) | v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v2_pre_topc(sK0) | (~spl5_14 | ~spl5_55)),
% 4.94/0.98    inference(resolution,[],[f396,f178])).
% 4.94/0.98  fof(f178,plain,(
% 4.94/0.98    v5_pre_topc(sK2,sK0,sK1) | ~spl5_14),
% 4.94/0.98    inference(avatar_component_clause,[],[f172])).
% 4.94/0.98  fof(f1315,plain,(
% 4.94/0.98    spl5_108 | ~spl5_34 | ~spl5_65 | ~spl5_76),
% 4.94/0.98    inference(avatar_split_clause,[],[f1266,f624,f545,f263,f1313])).
% 4.94/0.98  fof(f1266,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_34 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(backward_demodulation,[],[f546,f1264])).
% 4.94/0.98  fof(f1299,plain,(
% 4.94/0.98    spl5_107 | ~spl5_34 | ~spl5_64 | ~spl5_65 | ~spl5_76),
% 4.94/0.98    inference(avatar_split_clause,[],[f1265,f624,f545,f538,f263,f1297])).
% 4.94/0.98  fof(f538,plain,(
% 4.94/0.98    spl5_64 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 4.94/0.98  fof(f1265,plain,(
% 4.94/0.98    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_34 | ~spl5_64 | ~spl5_65 | ~spl5_76)),
% 4.94/0.98    inference(backward_demodulation,[],[f539,f1264])).
% 4.94/0.98  fof(f539,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl5_64),
% 4.94/0.98    inference(avatar_component_clause,[],[f538])).
% 4.94/0.98  fof(f1295,plain,(
% 4.94/0.98    spl5_106 | ~spl5_34 | ~spl5_65 | ~spl5_76),
% 4.94/0.98    inference(avatar_split_clause,[],[f1264,f624,f545,f263,f1293])).
% 4.94/0.98  fof(f1134,plain,(
% 4.94/0.98    spl5_103 | ~spl5_64 | ~spl5_74),
% 4.94/0.98    inference(avatar_split_clause,[],[f1060,f617,f538,f1132])).
% 4.94/0.98  fof(f1060,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_64 | ~spl5_74)),
% 4.94/0.98    inference(backward_demodulation,[],[f539,f618])).
% 4.94/0.98  fof(f618,plain,(
% 4.94/0.98    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_74),
% 4.94/0.98    inference(avatar_component_clause,[],[f617])).
% 4.94/0.98  fof(f1044,plain,(
% 4.94/0.98    spl5_100 | ~spl5_37 | ~spl5_46),
% 4.94/0.98    inference(avatar_split_clause,[],[f366,f335,f275,f1042])).
% 4.94/0.98  fof(f275,plain,(
% 4.94/0.98    spl5_37 <=> ! [X1,X3,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 4.94/0.98  fof(f335,plain,(
% 4.94/0.98    spl5_46 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 4.94/0.98  fof(f366,plain,(
% 4.94/0.98    ( ! [X6,X4,X2,X7,X5,X3] : (~m1_subset_1(k2_partfun1(X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k1_relset_1(X6,X7,k2_partfun1(X2,X3,X4,X5)) != X6 | v1_funct_2(k2_partfun1(X2,X3,X4,X5),X6,X7) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) ) | (~spl5_37 | ~spl5_46)),
% 4.94/0.98    inference(resolution,[],[f336,f276])).
% 4.94/0.98  fof(f276,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_1(k2_partfun1(X0,X1,X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl5_37),
% 4.94/0.98    inference(avatar_component_clause,[],[f275])).
% 4.94/0.98  fof(f336,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) ) | ~spl5_46),
% 4.94/0.98    inference(avatar_component_clause,[],[f335])).
% 4.94/0.98  fof(f1026,plain,(
% 4.94/0.98    spl5_98 | ~spl5_10 | ~spl5_21 | ~spl5_45 | ~spl5_56 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f814,f773,f422,f331,f203,f156,f1024])).
% 4.94/0.98  fof(f773,plain,(
% 4.94/0.98    spl5_79 <=> v1_xboole_0(sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 4.94/0.98  fof(f814,plain,(
% 4.94/0.98    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | (~spl5_10 | ~spl5_21 | ~spl5_45 | ~spl5_56 | ~spl5_79)),
% 4.94/0.98    inference(subsumption_resolution,[],[f813,f157])).
% 4.94/0.98  fof(f813,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1))) ) | (~spl5_21 | ~spl5_45 | ~spl5_56 | ~spl5_79)),
% 4.94/0.98    inference(forward_demodulation,[],[f788,f782])).
% 4.94/0.98  fof(f782,plain,(
% 4.94/0.98    k1_xboole_0 = sK2 | (~spl5_21 | ~spl5_79)),
% 4.94/0.98    inference(resolution,[],[f774,f204])).
% 4.94/0.98  fof(f774,plain,(
% 4.94/0.98    v1_xboole_0(sK2) | ~spl5_79),
% 4.94/0.98    inference(avatar_component_clause,[],[f773])).
% 4.94/0.98  fof(f788,plain,(
% 4.94/0.98    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_21 | ~spl5_45 | ~spl5_56 | ~spl5_79)),
% 4.94/0.98    inference(backward_demodulation,[],[f426,f782])).
% 4.94/0.98  fof(f426,plain,(
% 4.94/0.98    ( ! [X0] : (v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_45 | ~spl5_56)),
% 4.94/0.98    inference(superposition,[],[f423,f332])).
% 4.94/0.98  fof(f1020,plain,(
% 4.94/0.98    spl5_97 | ~spl5_44 | ~spl5_47),
% 4.94/0.98    inference(avatar_split_clause,[],[f373,f339,f319,f1018])).
% 4.94/0.98  fof(f373,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl5_44 | ~spl5_47)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f371])).
% 4.94/0.98  fof(f371,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relat_1(X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | (~spl5_44 | ~spl5_47)),
% 4.94/0.98    inference(superposition,[],[f340,f320])).
% 4.94/0.98  fof(f997,plain,(
% 4.94/0.98    spl5_94 | ~spl5_21 | ~spl5_34 | ~spl5_41 | ~spl5_43),
% 4.94/0.98    inference(avatar_split_clause,[],[f329,f315,f304,f263,f203,f995])).
% 4.94/0.98  fof(f304,plain,(
% 4.94/0.98    spl5_41 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 4.94/0.98  fof(f315,plain,(
% 4.94/0.98    spl5_43 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(k1_relat_1(X0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 4.94/0.98  fof(f329,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl5_21 | ~spl5_34 | ~spl5_41 | ~spl5_43)),
% 4.94/0.98    inference(subsumption_resolution,[],[f328,f325])).
% 4.94/0.98  fof(f325,plain,(
% 4.94/0.98    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X8))) | k1_xboole_0 = k1_relat_1(X7)) ) | (~spl5_21 | ~spl5_43)),
% 4.94/0.98    inference(resolution,[],[f316,f204])).
% 4.94/0.98  fof(f316,plain,(
% 4.94/0.98    ( ! [X0,X1] : (v1_xboole_0(k1_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) ) | ~spl5_43),
% 4.94/0.98    inference(avatar_component_clause,[],[f315])).
% 4.94/0.98  fof(f328,plain,(
% 4.94/0.98    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl5_34 | ~spl5_41)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f327])).
% 4.94/0.98  fof(f327,plain,(
% 4.94/0.98    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl5_34 | ~spl5_41)),
% 4.94/0.98    inference(superposition,[],[f305,f264])).
% 4.94/0.98  fof(f305,plain,(
% 4.94/0.98    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl5_41),
% 4.94/0.98    inference(avatar_component_clause,[],[f304])).
% 4.94/0.98  fof(f876,plain,(
% 4.94/0.98    spl5_85 | ~spl5_58 | ~spl5_74),
% 4.94/0.98    inference(avatar_split_clause,[],[f711,f617,f433,f874])).
% 4.94/0.98  fof(f711,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(sK0) | (~spl5_58 | ~spl5_74)),
% 4.94/0.98    inference(backward_demodulation,[],[f434,f618])).
% 4.94/0.98  fof(f859,plain,(
% 4.94/0.98    spl5_83 | ~spl5_21 | ~spl5_74 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f795,f773,f617,f203,f857])).
% 4.94/0.98  fof(f795,plain,(
% 4.94/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_21 | ~spl5_74 | ~spl5_79)),
% 4.94/0.98    inference(backward_demodulation,[],[f618,f782])).
% 4.94/0.98  fof(f842,plain,(
% 4.94/0.98    spl5_82 | ~spl5_14 | ~spl5_21 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f786,f773,f203,f172,f840])).
% 4.94/0.98  fof(f786,plain,(
% 4.94/0.98    v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl5_14 | ~spl5_21 | ~spl5_79)),
% 4.94/0.98    inference(backward_demodulation,[],[f178,f782])).
% 4.94/0.98  fof(f838,plain,(
% 4.94/0.98    spl5_81 | ~spl5_6 | ~spl5_21 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f785,f773,f203,f140,f836])).
% 4.94/0.98  fof(f785,plain,(
% 4.94/0.98    k1_xboole_0 = sK3 | (~spl5_6 | ~spl5_21 | ~spl5_79)),
% 4.94/0.98    inference(backward_demodulation,[],[f141,f782])).
% 4.94/0.98  fof(f834,plain,(
% 4.94/0.98    spl5_73 | ~spl5_21 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f782,f773,f203,f614])).
% 4.94/0.98  fof(f832,plain,(
% 4.94/0.98    spl5_77 | ~spl5_1 | ~spl5_21 | ~spl5_79),
% 4.94/0.98    inference(avatar_split_clause,[],[f784,f773,f203,f120,f705])).
% 4.94/0.98  fof(f784,plain,(
% 4.94/0.98    v1_funct_1(k1_xboole_0) | (~spl5_1 | ~spl5_21 | ~spl5_79)),
% 4.94/0.98    inference(backward_demodulation,[],[f121,f782])).
% 4.94/0.98  fof(f775,plain,(
% 4.94/0.98    spl5_79 | ~spl5_27 | ~spl5_72),
% 4.94/0.98    inference(avatar_split_clause,[],[f765,f611,f229,f773])).
% 4.94/0.98  fof(f765,plain,(
% 4.94/0.98    v1_xboole_0(sK2) | (~spl5_27 | ~spl5_72)),
% 4.94/0.98    inference(resolution,[],[f763,f230])).
% 4.94/0.98  fof(f763,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_72),
% 4.94/0.98    inference(avatar_component_clause,[],[f611])).
% 4.94/0.98  fof(f626,plain,(
% 4.94/0.98    spl5_75 | spl5_76 | ~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f510,f433,f356,f168,f160,f624,f621])).
% 4.94/0.98  fof(f510,plain,(
% 4.94/0.98    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl5_11 | ~spl5_13 | ~spl5_50 | ~spl5_58)),
% 4.94/0.98    inference(backward_demodulation,[],[f382,f434])).
% 4.94/0.98  fof(f561,plain,(
% 4.94/0.98    spl5_68),
% 4.94/0.98    inference(avatar_split_clause,[],[f112,f559])).
% 4.94/0.98  fof(f112,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f100])).
% 4.94/0.98  fof(f100,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(equality_resolution,[],[f76])).
% 4.94/0.98  fof(f76,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f32])).
% 4.94/0.98  fof(f32,plain,(
% 4.94/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.94/0.98    inference(flattening,[],[f31])).
% 4.94/0.98  fof(f31,plain,(
% 4.94/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.94/0.98    inference(ennf_transformation,[],[f21])).
% 4.94/0.98  fof(f21,axiom,(
% 4.94/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 4.94/0.98  fof(f556,plain,(
% 4.94/0.98    spl5_67),
% 4.94/0.98    inference(avatar_split_clause,[],[f111,f554])).
% 4.94/0.98  fof(f111,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f101])).
% 4.94/0.98  fof(f101,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(equality_resolution,[],[f75])).
% 4.94/0.98  fof(f75,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f32])).
% 4.94/0.98  fof(f551,plain,(
% 4.94/0.98    spl5_66 | ~spl5_5 | ~spl5_22 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f521,f433,f207,f136,f549])).
% 4.94/0.98  fof(f521,plain,(
% 4.94/0.98    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | (~spl5_5 | ~spl5_22 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f518,f137])).
% 4.94/0.98  fof(f518,plain,(
% 4.94/0.98    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(k1_relat_1(sK2)))) | ~l1_pre_topc(sK0) | (~spl5_22 | ~spl5_58)),
% 4.94/0.98    inference(superposition,[],[f208,f434])).
% 4.94/0.98  fof(f547,plain,(
% 4.94/0.98    spl5_65 | ~spl5_13 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f508,f433,f168,f545])).
% 4.94/0.98  fof(f508,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl5_13 | ~spl5_58)),
% 4.94/0.98    inference(backward_demodulation,[],[f169,f434])).
% 4.94/0.98  fof(f540,plain,(
% 4.94/0.98    spl5_64 | ~spl5_11 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f507,f433,f160,f538])).
% 4.94/0.98  fof(f507,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl5_11 | ~spl5_58)),
% 4.94/0.98    inference(backward_demodulation,[],[f161,f434])).
% 4.94/0.98  fof(f530,plain,(
% 4.94/0.98    ~spl5_62 | spl5_15 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f509,f433,f175,f528])).
% 4.94/0.98  fof(f509,plain,(
% 4.94/0.98    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (spl5_15 | ~spl5_58)),
% 4.94/0.98    inference(backward_demodulation,[],[f176,f434])).
% 4.94/0.98  fof(f475,plain,(
% 4.94/0.98    spl5_60 | ~spl5_4 | ~spl5_5 | ~spl5_29 | ~spl5_58),
% 4.94/0.98    inference(avatar_split_clause,[],[f465,f433,f237,f136,f132,f473])).
% 4.94/0.98  fof(f465,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl5_4 | ~spl5_5 | ~spl5_29 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f464,f133])).
% 4.94/0.98  fof(f464,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~v2_pre_topc(sK0) | (~spl5_5 | ~spl5_29 | ~spl5_58)),
% 4.94/0.98    inference(subsumption_resolution,[],[f461,f137])).
% 4.94/0.98  fof(f461,plain,(
% 4.94/0.98    v2_pre_topc(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_29 | ~spl5_58)),
% 4.94/0.98    inference(superposition,[],[f238,f434])).
% 4.94/0.98  fof(f435,plain,(
% 4.94/0.98    spl5_58 | ~spl5_9 | ~spl5_34 | ~spl5_52),
% 4.94/0.98    inference(avatar_split_clause,[],[f405,f384,f263,f152,f433])).
% 4.94/0.98  fof(f384,plain,(
% 4.94/0.98    spl5_52 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 4.94/0.98  fof(f405,plain,(
% 4.94/0.98    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl5_9 | ~spl5_34 | ~spl5_52)),
% 4.94/0.98    inference(subsumption_resolution,[],[f398,f153])).
% 4.94/0.98  fof(f398,plain,(
% 4.94/0.98    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl5_34 | ~spl5_52)),
% 4.94/0.98    inference(superposition,[],[f385,f264])).
% 4.94/0.98  fof(f385,plain,(
% 4.94/0.98    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl5_52),
% 4.94/0.98    inference(avatar_component_clause,[],[f384])).
% 4.94/0.98  fof(f430,plain,(
% 4.94/0.98    spl5_57 | ~spl5_9 | ~spl5_34 | ~spl5_52),
% 4.94/0.98    inference(avatar_split_clause,[],[f407,f384,f263,f152,f428])).
% 4.94/0.98  fof(f407,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl5_9 | ~spl5_34 | ~spl5_52)),
% 4.94/0.98    inference(backward_demodulation,[],[f153,f405])).
% 4.94/0.98  fof(f424,plain,(
% 4.94/0.98    spl5_56 | ~spl5_7 | ~spl5_9 | ~spl5_34 | ~spl5_52),
% 4.94/0.98    inference(avatar_split_clause,[],[f406,f384,f263,f152,f144,f422])).
% 4.94/0.98  fof(f144,plain,(
% 4.94/0.98    spl5_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 4.94/0.98  fof(f406,plain,(
% 4.94/0.98    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl5_7 | ~spl5_9 | ~spl5_34 | ~spl5_52)),
% 4.94/0.98    inference(backward_demodulation,[],[f145,f405])).
% 4.94/0.98  fof(f145,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl5_7),
% 4.94/0.98    inference(avatar_component_clause,[],[f144])).
% 4.94/0.98  fof(f397,plain,(
% 4.94/0.98    spl5_55),
% 4.94/0.98    inference(avatar_split_clause,[],[f110,f395])).
% 4.94/0.98  fof(f110,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f102])).
% 4.94/0.98  fof(f102,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(equality_resolution,[],[f78])).
% 4.94/0.98  fof(f78,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f34])).
% 4.94/0.98  fof(f34,plain,(
% 4.94/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.94/0.98    inference(flattening,[],[f33])).
% 4.94/0.98  fof(f33,plain,(
% 4.94/0.98    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.94/0.98    inference(ennf_transformation,[],[f20])).
% 4.94/0.98  fof(f20,axiom,(
% 4.94/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 4.94/0.98  fof(f393,plain,(
% 4.94/0.98    spl5_54),
% 4.94/0.98    inference(avatar_split_clause,[],[f109,f391])).
% 4.94/0.98  fof(f109,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f103])).
% 4.94/0.98  fof(f103,plain,(
% 4.94/0.98    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 4.94/0.98    inference(equality_resolution,[],[f77])).
% 4.94/0.98  fof(f77,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f34])).
% 4.94/0.98  fof(f389,plain,(
% 4.94/0.98    spl5_52 | spl5_53 | ~spl5_7 | ~spl5_9 | ~spl5_50),
% 4.94/0.98    inference(avatar_split_clause,[],[f381,f356,f152,f144,f387,f384])).
% 4.94/0.98  fof(f381,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl5_7 | ~spl5_9 | ~spl5_50)),
% 4.94/0.98    inference(subsumption_resolution,[],[f378,f153])).
% 4.94/0.98  fof(f378,plain,(
% 4.94/0.98    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | (~spl5_7 | ~spl5_50)),
% 4.94/0.98    inference(resolution,[],[f357,f145])).
% 4.94/0.98  fof(f358,plain,(
% 4.94/0.98    spl5_50),
% 4.94/0.98    inference(avatar_split_clause,[],[f94,f356])).
% 4.94/0.98  fof(f94,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f45])).
% 4.94/0.98  fof(f45,plain,(
% 4.94/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    inference(flattening,[],[f44])).
% 4.94/0.98  fof(f44,plain,(
% 4.94/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    inference(ennf_transformation,[],[f13])).
% 4.94/0.98  fof(f13,axiom,(
% 4.94/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 4.94/0.98  fof(f341,plain,(
% 4.94/0.98    spl5_47),
% 4.94/0.98    inference(avatar_split_clause,[],[f99,f339])).
% 4.94/0.98  fof(f99,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f53])).
% 4.94/0.98  fof(f53,plain,(
% 4.94/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    inference(flattening,[],[f52])).
% 4.94/0.98  fof(f52,plain,(
% 4.94/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.94/0.98    inference(ennf_transformation,[],[f14])).
% 4.94/0.98  fof(f14,axiom,(
% 4.94/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (m1_subset_1(k2_partfun1(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(k2_partfun1(X0,X1,X2,X3))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).
% 4.94/0.98  fof(f337,plain,(
% 4.94/0.98    spl5_46),
% 4.94/0.98    inference(avatar_split_clause,[],[f95,f335])).
% 4.94/0.98  fof(f95,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f47])).
% 4.94/0.98  fof(f47,plain,(
% 4.94/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    inference(flattening,[],[f46])).
% 4.94/0.98  fof(f46,plain,(
% 4.94/0.98    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | k1_relset_1(X0,X1,X2) != X0) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.94/0.98    inference(ennf_transformation,[],[f16])).
% 4.94/0.98  fof(f16,axiom,(
% 4.94/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (k1_relset_1(X0,X1,X2) = X0 => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).
% 4.94/0.98  fof(f333,plain,(
% 4.94/0.98    spl5_45 | ~spl5_21 | ~spl5_43),
% 4.94/0.98    inference(avatar_split_clause,[],[f325,f315,f203,f331])).
% 4.94/0.98  fof(f321,plain,(
% 4.94/0.98    spl5_44),
% 4.94/0.98    inference(avatar_split_clause,[],[f97,f319])).
% 4.94/0.98  fof(f97,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f51])).
% 4.94/0.98  fof(f51,plain,(
% 4.94/0.98    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 4.94/0.98    inference(flattening,[],[f50])).
% 4.94/0.98  fof(f50,plain,(
% 4.94/0.98    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 4.94/0.98    inference(ennf_transformation,[],[f15])).
% 4.94/0.98  fof(f15,axiom,(
% 4.94/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 4.94/0.98  fof(f317,plain,(
% 4.94/0.98    spl5_43 | ~spl5_27 | ~spl5_40),
% 4.94/0.98    inference(avatar_split_clause,[],[f311,f300,f229,f315])).
% 4.94/0.98  fof(f300,plain,(
% 4.94/0.98    spl5_40 <=> ! [X1,X0,X2] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 4.94/0.98  fof(f311,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(k1_relat_1(X0))) ) | (~spl5_27 | ~spl5_40)),
% 4.94/0.98    inference(resolution,[],[f301,f230])).
% 4.94/0.98  fof(f301,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_40),
% 4.94/0.98    inference(avatar_component_clause,[],[f300])).
% 4.94/0.98  fof(f306,plain,(
% 4.94/0.98    spl5_41),
% 4.94/0.98    inference(avatar_split_clause,[],[f105,f304])).
% 4.94/0.98  fof(f105,plain,(
% 4.94/0.98    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 4.94/0.98    inference(equality_resolution,[],[f91])).
% 4.94/0.98  fof(f91,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f45])).
% 4.94/0.98  fof(f302,plain,(
% 4.94/0.98    spl5_40 | ~spl5_34 | ~spl5_36),
% 4.94/0.98    inference(avatar_split_clause,[],[f294,f271,f263,f300])).
% 4.94/0.98  fof(f271,plain,(
% 4.94/0.98    spl5_36 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 4.94/0.98  fof(f294,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_34 | ~spl5_36)),
% 4.94/0.98    inference(duplicate_literal_removal,[],[f293])).
% 4.94/0.98  fof(f293,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_34 | ~spl5_36)),
% 4.94/0.98    inference(superposition,[],[f272,f264])).
% 4.94/0.98  fof(f272,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_36),
% 4.94/0.98    inference(avatar_component_clause,[],[f271])).
% 4.94/0.98  fof(f291,plain,(
% 4.94/0.98    spl5_38 | ~spl5_21 | ~spl5_35),
% 4.94/0.98    inference(avatar_split_clause,[],[f280,f267,f203,f289])).
% 4.94/0.98  fof(f267,plain,(
% 4.94/0.98    spl5_35 <=> ! [X0] : v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 4.94/0.98  fof(f280,plain,(
% 4.94/0.98    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(X5,k1_xboole_0)) ) | (~spl5_21 | ~spl5_35)),
% 4.94/0.98    inference(resolution,[],[f268,f204])).
% 4.94/0.98  fof(f268,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | ~spl5_35),
% 4.94/0.98    inference(avatar_component_clause,[],[f267])).
% 4.94/0.98  fof(f277,plain,(
% 4.94/0.98    spl5_37),
% 4.94/0.98    inference(avatar_split_clause,[],[f98,f275])).
% 4.94/0.98  fof(f98,plain,(
% 4.94/0.98    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_1(k2_partfun1(X0,X1,X2,X3))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f53])).
% 4.94/0.98  fof(f273,plain,(
% 4.94/0.98    spl5_36),
% 4.94/0.98    inference(avatar_split_clause,[],[f86,f271])).
% 4.94/0.98  fof(f86,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f42])).
% 4.94/0.98  fof(f42,plain,(
% 4.94/0.98    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    inference(ennf_transformation,[],[f11])).
% 4.94/0.98  fof(f11,axiom,(
% 4.94/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).
% 4.94/0.98  fof(f269,plain,(
% 4.94/0.98    spl5_35 | ~spl5_12 | ~spl5_16 | ~spl5_33),
% 4.94/0.98    inference(avatar_split_clause,[],[f261,f256,f182,f164,f267])).
% 4.94/0.98  fof(f164,plain,(
% 4.94/0.98    spl5_12 <=> ! [X0] : (v1_xboole_0(X0) | ~v1_xboole_0(sK4(X0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 4.94/0.98  fof(f182,plain,(
% 4.94/0.98    spl5_16 <=> ! [X0] : (v1_xboole_0(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(X0)))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 4.94/0.98  fof(f256,plain,(
% 4.94/0.98    spl5_33 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 4.94/0.98  fof(f261,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | (~spl5_12 | ~spl5_16 | ~spl5_33)),
% 4.94/0.98    inference(subsumption_resolution,[],[f260,f165])).
% 4.94/0.98  fof(f165,plain,(
% 4.94/0.98    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | v1_xboole_0(X0)) ) | ~spl5_12),
% 4.94/0.98    inference(avatar_component_clause,[],[f164])).
% 4.94/0.98  fof(f260,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(sK4(k2_zfmisc_1(X0,k1_xboole_0))) | v1_xboole_0(k2_zfmisc_1(X0,k1_xboole_0))) ) | (~spl5_16 | ~spl5_33)),
% 4.94/0.98    inference(resolution,[],[f257,f183])).
% 4.94/0.98  fof(f183,plain,(
% 4.94/0.98    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(X0)) | v1_xboole_0(X0)) ) | ~spl5_16),
% 4.94/0.98    inference(avatar_component_clause,[],[f182])).
% 4.94/0.98  fof(f257,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | ~spl5_33),
% 4.94/0.98    inference(avatar_component_clause,[],[f256])).
% 4.94/0.98  fof(f265,plain,(
% 4.94/0.98    spl5_34),
% 4.94/0.98    inference(avatar_split_clause,[],[f85,f263])).
% 4.94/0.98  fof(f85,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f41])).
% 4.94/0.98  fof(f41,plain,(
% 4.94/0.98    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.94/0.98    inference(ennf_transformation,[],[f12])).
% 4.94/0.98  fof(f12,axiom,(
% 4.94/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 4.94/0.98  fof(f258,plain,(
% 4.94/0.98    spl5_33 | ~spl5_8 | ~spl5_30),
% 4.94/0.98    inference(avatar_split_clause,[],[f254,f243,f148,f256])).
% 4.94/0.98  fof(f148,plain,(
% 4.94/0.98    spl5_8 <=> v1_xboole_0(k1_xboole_0)),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 4.94/0.98  fof(f243,plain,(
% 4.94/0.98    spl5_30 <=> ! [X1,X0,X2] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 4.94/0.98  fof(f254,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) | v1_xboole_0(X0)) ) | (~spl5_8 | ~spl5_30)),
% 4.94/0.98    inference(resolution,[],[f244,f149])).
% 4.94/0.98  fof(f149,plain,(
% 4.94/0.98    v1_xboole_0(k1_xboole_0) | ~spl5_8),
% 4.94/0.98    inference(avatar_component_clause,[],[f148])).
% 4.94/0.98  fof(f244,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) ) | ~spl5_30),
% 4.94/0.98    inference(avatar_component_clause,[],[f243])).
% 4.94/0.98  fof(f245,plain,(
% 4.94/0.98    spl5_30),
% 4.94/0.98    inference(avatar_split_clause,[],[f79,f243])).
% 4.94/0.98  fof(f79,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f35])).
% 4.94/0.98  fof(f35,plain,(
% 4.94/0.98    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 4.94/0.98    inference(ennf_transformation,[],[f10])).
% 4.94/0.98  fof(f10,axiom,(
% 4.94/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).
% 4.94/0.98  fof(f239,plain,(
% 4.94/0.98    spl5_29),
% 4.94/0.98    inference(avatar_split_clause,[],[f74,f237])).
% 4.94/0.98  fof(f74,plain,(
% 4.94/0.98    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f30])).
% 4.94/0.98  fof(f30,plain,(
% 4.94/0.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 4.94/0.98    inference(flattening,[],[f29])).
% 4.94/0.98  fof(f29,plain,(
% 4.94/0.98    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 4.94/0.98    inference(ennf_transformation,[],[f19])).
% 4.94/0.98  fof(f19,axiom,(
% 4.94/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 4.94/0.98  fof(f231,plain,(
% 4.94/0.98    spl5_27 | ~spl5_8 | ~spl5_19),
% 4.94/0.98    inference(avatar_split_clause,[],[f227,f194,f148,f229])).
% 4.94/0.98  fof(f194,plain,(
% 4.94/0.98    spl5_19 <=> ! [X1,X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 4.94/0.98  fof(f227,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | (~spl5_8 | ~spl5_19)),
% 4.94/0.98    inference(resolution,[],[f195,f149])).
% 4.94/0.98  fof(f195,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) ) | ~spl5_19),
% 4.94/0.98    inference(avatar_component_clause,[],[f194])).
% 4.94/0.98  fof(f218,plain,(
% 4.94/0.98    spl5_24),
% 4.94/0.98    inference(avatar_split_clause,[],[f81,f216])).
% 4.94/0.98  fof(f81,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f36])).
% 4.94/0.98  fof(f36,plain,(
% 4.94/0.98    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 4.94/0.98    inference(ennf_transformation,[],[f17])).
% 4.94/0.98  fof(f17,axiom,(
% 4.94/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 4.94/0.98  fof(f209,plain,(
% 4.94/0.98    spl5_22),
% 4.94/0.98    inference(avatar_split_clause,[],[f71,f207])).
% 4.94/0.98  fof(f71,plain,(
% 4.94/0.98    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f27])).
% 4.94/0.98  fof(f27,plain,(
% 4.94/0.98    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 4.94/0.98    inference(ennf_transformation,[],[f18])).
% 4.94/0.98  fof(f18,axiom,(
% 4.94/0.98    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 4.94/0.98  fof(f205,plain,(
% 4.94/0.98    spl5_21 | ~spl5_8 | ~spl5_17),
% 4.94/0.98    inference(avatar_split_clause,[],[f201,f186,f148,f203])).
% 4.94/0.98  fof(f186,plain,(
% 4.94/0.98    spl5_17 <=> ! [X1,X0] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1))),
% 4.94/0.98    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 4.94/0.98  fof(f201,plain,(
% 4.94/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl5_8 | ~spl5_17)),
% 4.94/0.98    inference(resolution,[],[f187,f149])).
% 4.94/0.98  fof(f187,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl5_17),
% 4.94/0.98    inference(avatar_component_clause,[],[f186])).
% 4.94/0.98  fof(f196,plain,(
% 4.94/0.98    spl5_19),
% 4.94/0.98    inference(avatar_split_clause,[],[f72,f194])).
% 4.94/0.98  fof(f72,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f28])).
% 4.94/0.98  fof(f28,plain,(
% 4.94/0.98    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 4.94/0.98    inference(ennf_transformation,[],[f5])).
% 4.94/0.98  fof(f5,axiom,(
% 4.94/0.98    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 4.94/0.98  fof(f192,plain,(
% 4.94/0.98    spl5_18),
% 4.94/0.98    inference(avatar_split_clause,[],[f118,f190])).
% 4.94/0.98  fof(f118,plain,(
% 4.94/0.98    ( ! [X0] : (k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 4.94/0.98    inference(subsumption_resolution,[],[f108,f68])).
% 4.94/0.98  fof(f68,plain,(
% 4.94/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f4])).
% 4.94/0.98  fof(f4,axiom,(
% 4.94/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 4.94/0.98  fof(f108,plain,(
% 4.94/0.98    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | v1_funct_2(k1_xboole_0,X0,k1_xboole_0)) )),
% 4.94/0.98    inference(equality_resolution,[],[f107])).
% 4.94/0.98  fof(f107,plain,(
% 4.94/0.98    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,k1_xboole_0)) )),
% 4.94/0.98    inference(equality_resolution,[],[f89])).
% 4.94/0.98  fof(f89,plain,(
% 4.94/0.98    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 != X2 | v1_funct_2(X2,X0,X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f45])).
% 4.94/0.98  fof(f188,plain,(
% 4.94/0.98    spl5_17),
% 4.94/0.98    inference(avatar_split_clause,[],[f83,f186])).
% 4.94/0.98  fof(f83,plain,(
% 4.94/0.98    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 4.94/0.98    inference(cnf_transformation,[],[f39])).
% 4.94/0.98  fof(f39,plain,(
% 4.94/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 4.94/0.98    inference(ennf_transformation,[],[f2])).
% 4.94/0.98  fof(f2,axiom,(
% 4.94/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 4.94/0.98  fof(f184,plain,(
% 4.94/0.98    spl5_16),
% 4.94/0.98    inference(avatar_split_clause,[],[f69,f182])).
% 4.94/0.98  fof(f69,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(X0) | m1_subset_1(sK4(X0),k1_zfmisc_1(X0))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f26])).
% 4.94/0.98  fof(f26,plain,(
% 4.94/0.98    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) | v1_xboole_0(X0))),
% 4.94/0.98    inference(ennf_transformation,[],[f3])).
% 4.94/0.98  fof(f3,axiom,(
% 4.94/0.98    ! [X0] : (~v1_xboole_0(X0) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_subset_1)).
% 4.94/0.98  fof(f180,plain,(
% 4.94/0.98    spl5_14 | spl5_15),
% 4.94/0.98    inference(avatar_split_clause,[],[f117,f175,f172])).
% 4.94/0.98  fof(f117,plain,(
% 4.94/0.98    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 4.94/0.98    inference(forward_demodulation,[],[f54,f59])).
% 4.94/0.98  fof(f59,plain,(
% 4.94/0.98    sK2 = sK3),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f25,plain,(
% 4.94/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 4.94/0.98    inference(flattening,[],[f24])).
% 4.94/0.98  fof(f24,plain,(
% 4.94/0.98    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 4.94/0.98    inference(ennf_transformation,[],[f23])).
% 4.94/0.98  fof(f23,negated_conjecture,(
% 4.94/0.98    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.94/0.98    inference(negated_conjecture,[],[f22])).
% 4.94/0.98  fof(f22,conjecture,(
% 4.94/0.98    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 4.94/0.98  fof(f54,plain,(
% 4.94/0.98    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f177,plain,(
% 4.94/0.98    ~spl5_14 | ~spl5_15),
% 4.94/0.98    inference(avatar_split_clause,[],[f116,f175,f172])).
% 4.94/0.98  fof(f116,plain,(
% 4.94/0.98    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 4.94/0.98    inference(forward_demodulation,[],[f55,f59])).
% 4.94/0.98  fof(f55,plain,(
% 4.94/0.98    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f170,plain,(
% 4.94/0.98    spl5_13),
% 4.94/0.98    inference(avatar_split_clause,[],[f113,f168])).
% 4.94/0.98  fof(f113,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.94/0.98    inference(forward_demodulation,[],[f58,f59])).
% 4.94/0.98  fof(f58,plain,(
% 4.94/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f166,plain,(
% 4.94/0.98    spl5_12),
% 4.94/0.98    inference(avatar_split_clause,[],[f70,f164])).
% 4.94/0.98  fof(f70,plain,(
% 4.94/0.98    ( ! [X0] : (v1_xboole_0(X0) | ~v1_xboole_0(sK4(X0))) )),
% 4.94/0.98    inference(cnf_transformation,[],[f26])).
% 4.94/0.98  fof(f162,plain,(
% 4.94/0.98    spl5_11),
% 4.94/0.98    inference(avatar_split_clause,[],[f114,f160])).
% 4.94/0.98  fof(f114,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    inference(forward_demodulation,[],[f57,f59])).
% 4.94/0.98  fof(f57,plain,(
% 4.94/0.98    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f158,plain,(
% 4.94/0.98    spl5_10),
% 4.94/0.98    inference(avatar_split_clause,[],[f68,f156])).
% 4.94/0.98  fof(f154,plain,(
% 4.94/0.98    spl5_9),
% 4.94/0.98    inference(avatar_split_clause,[],[f62,f152])).
% 4.94/0.98  fof(f62,plain,(
% 4.94/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f150,plain,(
% 4.94/0.98    spl5_8),
% 4.94/0.98    inference(avatar_split_clause,[],[f67,f148])).
% 4.94/0.98  fof(f67,plain,(
% 4.94/0.98    v1_xboole_0(k1_xboole_0)),
% 4.94/0.98    inference(cnf_transformation,[],[f1])).
% 4.94/0.98  fof(f1,axiom,(
% 4.94/0.98    v1_xboole_0(k1_xboole_0)),
% 4.94/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 4.94/0.98  fof(f146,plain,(
% 4.94/0.98    spl5_7),
% 4.94/0.98    inference(avatar_split_clause,[],[f61,f144])).
% 4.94/0.98  fof(f61,plain,(
% 4.94/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f142,plain,(
% 4.94/0.98    spl5_6),
% 4.94/0.98    inference(avatar_split_clause,[],[f59,f140])).
% 4.94/0.98  fof(f138,plain,(
% 4.94/0.98    spl5_5),
% 4.94/0.98    inference(avatar_split_clause,[],[f66,f136])).
% 4.94/0.98  fof(f66,plain,(
% 4.94/0.98    l1_pre_topc(sK0)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f134,plain,(
% 4.94/0.98    spl5_4),
% 4.94/0.98    inference(avatar_split_clause,[],[f65,f132])).
% 4.94/0.98  fof(f65,plain,(
% 4.94/0.98    v2_pre_topc(sK0)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f130,plain,(
% 4.94/0.98    spl5_3),
% 4.94/0.98    inference(avatar_split_clause,[],[f64,f128])).
% 4.94/0.98  fof(f64,plain,(
% 4.94/0.98    l1_pre_topc(sK1)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f126,plain,(
% 4.94/0.98    spl5_2),
% 4.94/0.98    inference(avatar_split_clause,[],[f63,f124])).
% 4.94/0.98  fof(f63,plain,(
% 4.94/0.98    v2_pre_topc(sK1)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  fof(f122,plain,(
% 4.94/0.98    spl5_1),
% 4.94/0.98    inference(avatar_split_clause,[],[f60,f120])).
% 4.94/0.98  fof(f60,plain,(
% 4.94/0.98    v1_funct_1(sK2)),
% 4.94/0.98    inference(cnf_transformation,[],[f25])).
% 4.94/0.98  % SZS output end Proof for theBenchmark
% 4.94/0.98  % (31178)------------------------------
% 4.94/0.98  % (31178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.94/0.98  % (31178)Termination reason: Refutation
% 4.94/0.98  
% 4.94/0.98  % (31178)Memory used [KB]: 14711
% 4.94/0.98  % (31178)Time elapsed: 0.573 s
% 4.94/0.98  % (31178)------------------------------
% 4.94/0.98  % (31178)------------------------------
% 4.94/0.98  % (31168)Success in time 0.631 s
%------------------------------------------------------------------------------
