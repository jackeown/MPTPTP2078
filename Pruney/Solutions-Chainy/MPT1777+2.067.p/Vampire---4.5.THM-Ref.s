%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:12 EST 2020

% Result     : Theorem 2.64s
% Output     : Refutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  297 ( 706 expanded)
%              Number of leaves         :   68 ( 343 expanded)
%              Depth                    :   51
%              Number of atoms          : 2130 (7059 expanded)
%              Number of equality atoms :   75 ( 748 expanded)
%              Maximal formula depth    :   32 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4928,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f200,f206,f218,f244,f270,f275,f284,f289,f294,f316,f324,f363,f364,f367,f370,f378,f386,f396,f447,f454,f806,f1005,f1107,f1131,f4927])).

fof(f4927,plain,
    ( spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(avatar_contradiction_clause,[],[f4926])).

fof(f4926,plain,
    ( $false
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(subsumption_resolution,[],[f4925,f313])).

fof(f313,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f312])).

fof(f312,plain,
    ( spl9_39
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f4925,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_43
    | ~ spl9_47
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(subsumption_resolution,[],[f4924,f395])).

fof(f395,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_43 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl9_43
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).

fof(f4924,plain,
    ( ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_47
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(subsumption_resolution,[],[f4923,f162])).

fof(f162,plain,
    ( ~ v2_struct_0(sK4)
    | spl9_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl9_13
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f4923,plain,
    ( v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_47
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(subsumption_resolution,[],[f4911,f435])).

fof(f435,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_47 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl9_47
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).

fof(f4911,plain,
    ( ~ v2_pre_topc(sK4)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK4,sK4)
    | ~ l1_pre_topc(sK4)
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113
    | ~ spl9_125 ),
    inference(resolution,[],[f4828,f1129])).

fof(f1129,plain,
    ( v1_tsep_1(sK4,sK4)
    | ~ spl9_125 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1127,plain,
    ( spl9_125
  <=> v1_tsep_1(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).

fof(f4828,plain,
    ( ! [X0] :
        ( ~ v1_tsep_1(sK4,X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4827,f306])).

fof(f306,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ spl9_38 ),
    inference(avatar_component_clause,[],[f305])).

fof(f305,plain,
    ( spl9_38
  <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).

fof(f4827,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4826,f385])).

fof(f385,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_42 ),
    inference(avatar_component_clause,[],[f383])).

fof(f383,plain,
    ( spl9_42
  <=> u1_struct_0(sK5) = k2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).

fof(f4826,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4825,f243])).

fof(f243,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl9_26
  <=> u1_struct_0(sK3) = k2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f4825,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4824,f301])).

fof(f301,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl9_37
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f4824,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4823,f385])).

fof(f4823,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3))))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4822,f243])).

fof(f4822,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_36
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4821,f293])).

fof(f293,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ spl9_36 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl9_36
  <=> m1_subset_1(sK7,k2_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).

fof(f4821,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7,k2_struct_0(sK5))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4820,f385])).

fof(f4820,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_32
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4819,f274])).

fof(f274,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ spl9_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl9_32
  <=> m1_subset_1(sK7,k2_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).

fof(f4819,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7,k2_struct_0(sK4))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4818,f377])).

fof(f377,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_41 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl9_41
  <=> u1_struct_0(sK4) = k2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).

fof(f4818,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_31
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_41
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4817,f633])).

fof(f633,plain,
    ( ! [X4] :
        ( m1_pre_topc(sK5,X4)
        | ~ m1_pre_topc(sK4,X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl9_31
    | ~ spl9_41 ),
    inference(forward_demodulation,[],[f596,f269])).

fof(f269,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ spl9_31 ),
    inference(avatar_component_clause,[],[f267])).

fof(f267,plain,
    ( spl9_31
  <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).

fof(f596,plain,
    ( ! [X4] :
        ( m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),X4)
        | ~ m1_pre_topc(sK4,X4)
        | ~ l1_pre_topc(X4) )
    | ~ spl9_41 ),
    inference(superposition,[],[f81,f377])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
            & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

fof(f4817,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4816,f177])).

fof(f177,plain,
    ( ~ v2_struct_0(sK3)
    | spl9_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl9_16
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f4816,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4815,f172])).

fof(f172,plain,
    ( v2_pre_topc(sK3)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl9_15
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f4815,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4814,f167])).

fof(f167,plain,
    ( l1_pre_topc(sK3)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl9_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f4814,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | spl9_13
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4813,f162])).

fof(f4813,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | spl9_11
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4812,f152])).

fof(f152,plain,
    ( ~ v2_struct_0(sK5)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl9_11
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f4812,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4811,f142])).

fof(f142,plain,
    ( v1_funct_1(sK6)
    | ~ spl9_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl9_9
  <=> v1_funct_1(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f4811,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4810,f1004])).

fof(f1004,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_113 ),
    inference(avatar_component_clause,[],[f1002])).

fof(f1002,plain,
    ( spl9_113
  <=> m1_pre_topc(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).

fof(f4810,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | spl9_1
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4799,f102])).

fof(f102,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl9_1
  <=> r1_tmap_1(sK5,sK3,sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f4799,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK5,sK3,sK6,sK7)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(duplicate_literal_removal,[],[f4786])).

fof(f4786,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | r1_tmap_1(sK5,sK3,sK6,sK7)
        | ~ m1_subset_1(sK7,u1_struct_0(sK4))
        | ~ m1_subset_1(sK7,u1_struct_0(sK5))
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_pre_topc(sK4,X0)
        | ~ v1_tsep_1(sK4,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | v2_struct_0(sK5)
        | v2_struct_0(sK4)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(resolution,[],[f4320,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | r1_tmap_1(X3,X0,X4,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X6)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( r1_tmap_1(X3,X0,X4,X5)
      | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
      | X5 != X6
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_pre_topc(X2,X3)
      | ~ m1_pre_topc(X2,X1)
      | ~ v1_tsep_1(X2,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X1)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X1)
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( r1_tmap_1(X3,X0,X4,X5)
                                  | ~ r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                                & ( r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)
                                  | ~ r1_tmap_1(X3,X0,X4,X5) ) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( r1_tmap_1(X3,X0,X4,X5)
                              <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) )
                              | X5 != X6
                              | ~ m1_subset_1(X6,u1_struct_0(X2)) )
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_pre_topc(X2,X3)
                      | ~ m1_pre_topc(X2,X1)
                      | ~ v1_tsep_1(X2,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                      | ~ v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X1)
              | v2_struct_0(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X1)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0))
                        & v1_funct_1(X4) )
                     => ( ( m1_pre_topc(X2,X3)
                          & m1_pre_topc(X2,X1)
                          & v1_tsep_1(X2,X1) )
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( X5 = X6
                                 => ( r1_tmap_1(X3,X0,X4,X5)
                                  <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

fof(f4320,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_38
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4319,f306])).

fof(f4319,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
        | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4318,f385])).

fof(f4318,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3))
        | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4317,f243])).

fof(f4317,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_37
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4316,f301])).

fof(f4316,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
        | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_42
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4315,f385])).

fof(f4315,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3))))
        | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_26
    | ~ spl9_113 ),
    inference(forward_demodulation,[],[f4314,f243])).

fof(f4314,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | spl9_19
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4313,f192])).

fof(f192,plain,
    ( ~ v2_struct_0(sK2)
    | spl9_19 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl9_19
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f4313,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_18
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4312,f187])).

fof(f187,plain,
    ( v2_pre_topc(sK2)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl9_18
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f4312,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_17
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4311,f182])).

fof(f182,plain,
    ( l1_pre_topc(sK2)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl9_17
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f4311,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_10
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4310,f147])).

fof(f147,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl9_10
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f4310,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_14
    | ~ spl9_15
    | spl9_16
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4309,f177])).

fof(f4309,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_14
    | ~ spl9_15
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4308,f172])).

fof(f4308,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_14
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4307,f167])).

fof(f4307,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_9
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4306,f142])).

fof(f4306,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_21
    | ~ spl9_113 ),
    inference(subsumption_resolution,[],[f4267,f1004])).

fof(f4267,plain,
    ( ! [X0] :
        ( r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7)
        | ~ m1_pre_topc(sK4,sK5)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
        | ~ v1_funct_1(sK6)
        | ~ m1_pre_topc(sK5,X0)
        | ~ l1_pre_topc(sK3)
        | ~ v2_pre_topc(sK3)
        | v2_struct_0(sK3)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK5,sK2)
        | ~ l1_pre_topc(sK2)
        | ~ v2_pre_topc(sK2)
        | v2_struct_0(sK2) )
    | ~ spl9_21 ),
    inference(superposition,[],[f205,f1192])).

fof(f1192,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1191,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X2,X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X2,X0)
              | ~ m1_pre_topc(X2,X1) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X1)
             => m1_pre_topc(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

fof(f1191,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f1178,f87])).

fof(f1178,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f1177])).

fof(f1177,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X5)
      | ~ m1_pre_topc(X0,X5)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X5)
      | ~ v2_pre_topc(X5)
      | v2_struct_0(X5)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ m1_pre_topc(X3,X4)
      | ~ m1_pre_topc(X0,X4)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X4)
      | ~ v2_pre_topc(X4)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f82,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
      | ~ m1_pre_topc(X3,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
      | ~ v1_funct_1(X4)
      | ~ m1_pre_topc(X3,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))
                      | ~ m1_pre_topc(X3,X2)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                      | ~ v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                      | ~ v1_funct_1(X4) )
                  | ~ m1_pre_topc(X3,X0) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ! [X3] :
                  ( m1_pre_topc(X3,X0)
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( m1_pre_topc(X3,X2)
                       => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

fof(f205,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_21 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl9_21
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f1131,plain,
    ( spl9_125
    | ~ spl9_124 ),
    inference(avatar_split_clause,[],[f1125,f1102,f1127])).

fof(f1102,plain,
    ( spl9_124
  <=> sP0(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).

fof(f1125,plain,
    ( v1_tsep_1(sK4,sK4)
    | ~ spl9_124 ),
    inference(resolution,[],[f1104,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_tsep_1(X1,X0) )
      & ( ( m1_pre_topc(X1,X0)
          & v1_tsep_1(X1,X0) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ( m1_pre_topc(X1,X0)
        & v1_tsep_1(X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1104,plain,
    ( sP0(sK4,sK4)
    | ~ spl9_124 ),
    inference(avatar_component_clause,[],[f1102])).

fof(f1107,plain,
    ( spl9_124
    | ~ spl9_49
    | ~ spl9_91 ),
    inference(avatar_split_clause,[],[f1106,f803,f451,f1102])).

fof(f451,plain,
    ( spl9_49
  <=> v3_pre_topc(k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).

fof(f803,plain,
    ( spl9_91
  <=> sP1(sK4,k2_struct_0(sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).

fof(f1106,plain,
    ( sP0(sK4,sK4)
    | ~ spl9_49
    | ~ spl9_91 ),
    inference(subsumption_resolution,[],[f1099,f453])).

fof(f453,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_49 ),
    inference(avatar_component_clause,[],[f451])).

fof(f1099,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK4),sK4)
    | sP0(sK4,sK4)
    | ~ spl9_91 ),
    inference(resolution,[],[f805,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | sP0(X0,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( sP0(X0,X2)
          | ~ v3_pre_topc(X1,X0) )
        & ( v3_pre_topc(X1,X0)
          | ~ sP0(X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X2,X1] :
      ( ( ( sP0(X0,X1)
          | ~ v3_pre_topc(X2,X0) )
        & ( v3_pre_topc(X2,X0)
          | ~ sP0(X0,X1) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( sP0(X0,X1)
      <=> v3_pre_topc(X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f805,plain,
    ( sP1(sK4,k2_struct_0(sK4),sK4)
    | ~ spl9_91 ),
    inference(avatar_component_clause,[],[f803])).

fof(f1005,plain,
    ( spl9_113
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(avatar_split_clause,[],[f1000,f393,f375,f312,f267,f1002])).

fof(f1000,plain,
    ( m1_pre_topc(sK4,sK5)
    | ~ spl9_31
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f999,f269])).

fof(f999,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43 ),
    inference(forward_demodulation,[],[f981,f377])).

fof(f981,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl9_39
    | ~ spl9_43 ),
    inference(unit_resulting_resolution,[],[f313,f313,f395,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f806,plain,
    ( spl9_91
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f801,f433,f393,f375,f312,f803])).

fof(f801,plain,
    ( sP1(sK4,k2_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_41
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(forward_demodulation,[],[f779,f377])).

fof(f779,plain,
    ( sP1(sK4,u1_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_43
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f435,f313,f395,f194])).

fof(f194,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f96,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( sP1(X0,u1_struct_0(X1),X1)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | u1_struct_0(X1) != X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( sP1(X0,X2,X1)
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_folding,[],[f36,f38,f37])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> v3_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

fof(f454,plain,
    ( spl9_49
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(avatar_split_clause,[],[f449,f433,f312,f451])).

fof(f449,plain,
    ( v3_pre_topc(k2_struct_0(sK4),sK4)
    | ~ spl9_39
    | ~ spl9_47 ),
    inference(unit_resulting_resolution,[],[f313,f435,f85])).

fof(f85,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f447,plain,
    ( spl9_47
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f446,f185,f180,f155,f433])).

fof(f155,plain,
    ( spl9_12
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f446,plain,
    ( v2_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f445,f187])).

fof(f445,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(subsumption_resolution,[],[f426,f182])).

fof(f426,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ spl9_12 ),
    inference(resolution,[],[f86,f157])).

fof(f157,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f396,plain,
    ( spl9_43
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f390,f312,f393])).

fof(f390,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl9_39 ),
    inference(unit_resulting_resolution,[],[f313,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f386,plain,
    ( spl9_42
    | ~ spl9_33 ),
    inference(avatar_split_clause,[],[f381,f277,f383])).

fof(f277,plain,
    ( spl9_33
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).

fof(f381,plain,
    ( u1_struct_0(sK5) = k2_struct_0(sK5)
    | ~ spl9_33 ),
    inference(unit_resulting_resolution,[],[f278,f73])).

fof(f73,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f278,plain,
    ( l1_struct_0(sK5)
    | ~ spl9_33 ),
    inference(avatar_component_clause,[],[f277])).

fof(f378,plain,
    ( spl9_41
    | ~ spl9_30 ),
    inference(avatar_split_clause,[],[f373,f263,f375])).

fof(f263,plain,
    ( spl9_30
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f373,plain,
    ( u1_struct_0(sK4) = k2_struct_0(sK4)
    | ~ spl9_30 ),
    inference(unit_resulting_resolution,[],[f264,f73])).

fof(f264,plain,
    ( l1_struct_0(sK4)
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f370,plain,
    ( spl9_40
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f329,f180,f145,f320])).

fof(f320,plain,
    ( spl9_40
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).

fof(f329,plain,
    ( l1_pre_topc(sK5)
    | ~ spl9_10
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f182,f147,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f367,plain,
    ( spl9_39
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f332,f180,f155,f312])).

fof(f332,plain,
    ( l1_pre_topc(sK4)
    | ~ spl9_12
    | ~ spl9_17 ),
    inference(unit_resulting_resolution,[],[f182,f157,f78])).

fof(f364,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))
    | ~ v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f363,plain,
    ( u1_struct_0(sK3) != k2_struct_0(sK3)
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f324,plain,
    ( ~ spl9_40
    | spl9_33 ),
    inference(avatar_split_clause,[],[f318,f277,f320])).

fof(f318,plain,
    ( ~ l1_pre_topc(sK5)
    | spl9_33 ),
    inference(resolution,[],[f279,f74])).

fof(f74,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f279,plain,
    ( ~ l1_struct_0(sK5)
    | spl9_33 ),
    inference(avatar_component_clause,[],[f277])).

fof(f316,plain,
    ( ~ spl9_39
    | spl9_30 ),
    inference(avatar_split_clause,[],[f310,f263,f312])).

fof(f310,plain,
    ( ~ l1_pre_topc(sK4)
    | spl9_30 ),
    inference(resolution,[],[f265,f74])).

fof(f265,plain,
    ( ~ l1_struct_0(sK4)
    | spl9_30 ),
    inference(avatar_component_clause,[],[f263])).

fof(f294,plain,
    ( ~ spl9_33
    | spl9_36
    | ~ spl9_5 ),
    inference(avatar_split_clause,[],[f239,f120,f291,f277])).

fof(f120,plain,
    ( spl9_5
  <=> m1_subset_1(sK7,u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f239,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK5))
    | ~ l1_struct_0(sK5)
    | ~ spl9_5 ),
    inference(superposition,[],[f122,f73])).

fof(f122,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK5))
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f289,plain,
    ( ~ spl9_33
    | spl9_35
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f238,f135,f286,f277])).

fof(f286,plain,
    ( spl9_35
  <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).

fof(f135,plain,
    ( spl9_8
  <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f238,plain,
    ( v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))
    | ~ l1_struct_0(sK5)
    | ~ spl9_8 ),
    inference(superposition,[],[f137,f73])).

fof(f137,plain,
    ( v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f284,plain,
    ( ~ spl9_33
    | spl9_34
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f237,f130,f281,f277])).

fof(f281,plain,
    ( spl9_34
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).

fof(f130,plain,
    ( spl9_7
  <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f237,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))
    | ~ l1_struct_0(sK5)
    | ~ spl9_7 ),
    inference(superposition,[],[f132,f73])).

fof(f132,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    | ~ spl9_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f275,plain,
    ( ~ spl9_30
    | spl9_32
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f236,f197,f272,f263])).

fof(f197,plain,
    ( spl9_20
  <=> m1_subset_1(sK7,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f236,plain,
    ( m1_subset_1(sK7,k2_struct_0(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_20 ),
    inference(superposition,[],[f199,f73])).

fof(f199,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f197])).

fof(f270,plain,
    ( ~ spl9_30
    | spl9_31
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f235,f125,f267,f263])).

fof(f125,plain,
    ( spl9_6
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f235,plain,
    ( sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))
    | ~ l1_struct_0(sK4)
    | ~ spl9_6 ),
    inference(superposition,[],[f127,f73])).

fof(f127,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f244,plain,
    ( spl9_26
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f232,f215,f241])).

fof(f215,plain,
    ( spl9_23
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f232,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3)
    | ~ spl9_23 ),
    inference(unit_resulting_resolution,[],[f217,f73])).

fof(f217,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f215])).

fof(f218,plain,
    ( spl9_23
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f207,f165,f215])).

fof(f207,plain,
    ( l1_struct_0(sK3)
    | ~ spl9_14 ),
    inference(unit_resulting_resolution,[],[f167,f74])).

fof(f206,plain,
    ( spl9_21
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f201,f110,f105,f203])).

fof(f105,plain,
    ( spl9_2
  <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f110,plain,
    ( spl9_3
  <=> sK7 = sK8 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f201,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f107,f112])).

fof(f112,plain,
    ( sK7 = sK8
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f107,plain,
    ( r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f200,plain,
    ( spl9_20
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f195,f115,f110,f197])).

fof(f115,plain,
    ( spl9_4
  <=> m1_subset_1(sK8,u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f195,plain,
    ( m1_subset_1(sK7,u1_struct_0(sK4))
    | ~ spl9_3
    | ~ spl9_4 ),
    inference(backward_demodulation,[],[f117,f112])).

fof(f117,plain,
    ( m1_subset_1(sK8,u1_struct_0(sK4))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f193,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f54,f190])).

fof(f54,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
    & sK7 = sK8
    & m1_subset_1(sK8,u1_struct_0(sK4))
    & m1_subset_1(sK7,u1_struct_0(sK5))
    & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
    & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
    & v1_funct_1(sK6)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f17,f46,f45,f44,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ? [X6] :
                                ( ~ r1_tmap_1(X3,X1,X4,X5)
                                & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                & X5 = X6
                                & m1_subset_1(X6,u1_struct_0(X2)) )
                            & m1_subset_1(X5,u1_struct_0(X3)) )
                        & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ? [X6] :
                            ( ~ r1_tmap_1(X3,X1,X4,X5)
                            & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6)
                            & X5 = X6
                            & m1_subset_1(X6,u1_struct_0(X2)) )
                        & m1_subset_1(X5,u1_struct_0(X3)) )
                    & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                    & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                    & v1_funct_1(X4) )
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ? [X6] :
                          ( ~ r1_tmap_1(X3,sK3,X4,X5)
                          & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                          & X5 = X6
                          & m1_subset_1(X6,u1_struct_0(X2)) )
                      & m1_subset_1(X5,u1_struct_0(X3)) )
                  & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                  & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                  & v1_funct_1(X4) )
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ? [X6] :
                        ( ~ r1_tmap_1(X3,sK3,X4,X5)
                        & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6)
                        & X5 = X6
                        & m1_subset_1(X6,u1_struct_0(X2)) )
                    & m1_subset_1(X5,u1_struct_0(X3)) )
                & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
                & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
                & v1_funct_1(X4) )
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ? [X6] :
                      ( ~ r1_tmap_1(X3,sK3,X4,X5)
                      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                      & X5 = X6
                      & m1_subset_1(X6,u1_struct_0(sK4)) )
                  & m1_subset_1(X5,u1_struct_0(X3)) )
              & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
              & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
              & v1_funct_1(X4) )
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ? [X6] :
                    ( ~ r1_tmap_1(X3,sK3,X4,X5)
                    & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6)
                    & X5 = X6
                    & m1_subset_1(X6,u1_struct_0(sK4)) )
                & m1_subset_1(X5,u1_struct_0(X3)) )
            & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3))))
            & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3))
            & v1_funct_1(X4) )
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ? [X6] :
                  ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                  & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                  & X5 = X6
                  & m1_subset_1(X6,u1_struct_0(sK4)) )
              & m1_subset_1(X5,u1_struct_0(sK5)) )
          & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
          & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
          & v1_funct_1(X4) )
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ? [X6] :
                ( ~ r1_tmap_1(sK5,sK3,X4,X5)
                & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6)
                & X5 = X6
                & m1_subset_1(X6,u1_struct_0(sK4)) )
            & m1_subset_1(X5,u1_struct_0(sK5)) )
        & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
        & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ? [X6] :
              ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
              & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
              & X5 = X6
              & m1_subset_1(X6,u1_struct_0(sK4)) )
          & m1_subset_1(X5,u1_struct_0(sK5)) )
      & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))
      & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X5] :
        ( ? [X6] :
            ( ~ r1_tmap_1(sK5,sK3,sK6,X5)
            & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
            & X5 = X6
            & m1_subset_1(X6,u1_struct_0(sK4)) )
        & m1_subset_1(X5,u1_struct_0(sK5)) )
   => ( ? [X6] :
          ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
          & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
          & sK7 = X6
          & m1_subset_1(X6,u1_struct_0(sK4)) )
      & m1_subset_1(sK7,u1_struct_0(sK5)) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X6] :
        ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
        & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6)
        & sK7 = X6
        & m1_subset_1(X6,u1_struct_0(sK4)) )
   => ( ~ r1_tmap_1(sK5,sK3,sK6,sK7)
      & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)
      & sK7 = sK8
      & m1_subset_1(sK8,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ? [X6] :
                              ( ~ r1_tmap_1(X3,X1,X4,X5)
                              & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                              & X5 = X6
                              & m1_subset_1(X6,u1_struct_0(X2)) )
                          & m1_subset_1(X5,u1_struct_0(X3)) )
                      & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                      & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                      & v1_funct_1(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                          & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                          & v1_funct_1(X4) )
                       => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                         => ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X3))
                             => ! [X6] :
                                  ( m1_subset_1(X6,u1_struct_0(X2))
                                 => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                      & X5 = X6 )
                                   => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1))))
                        & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1))
                        & v1_funct_1(X4) )
                     => ( g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3
                       => ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X3))
                           => ! [X6] :
                                ( m1_subset_1(X6,u1_struct_0(X2))
                               => ( ( r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6)
                                    & X5 = X6 )
                                 => r1_tmap_1(X3,X1,X4,X5) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

fof(f188,plain,(
    spl9_18 ),
    inference(avatar_split_clause,[],[f55,f185])).

fof(f55,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f183,plain,(
    spl9_17 ),
    inference(avatar_split_clause,[],[f56,f180])).

fof(f56,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f178,plain,(
    ~ spl9_16 ),
    inference(avatar_split_clause,[],[f57,f175])).

fof(f57,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f173,plain,(
    spl9_15 ),
    inference(avatar_split_clause,[],[f58,f170])).

fof(f58,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f168,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f59,f165])).

fof(f59,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f163,plain,(
    ~ spl9_13 ),
    inference(avatar_split_clause,[],[f60,f160])).

fof(f60,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f158,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f61,f155])).

fof(f61,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f153,plain,(
    ~ spl9_11 ),
    inference(avatar_split_clause,[],[f62,f150])).

fof(f62,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f148,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f63,f145])).

fof(f63,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f143,plain,(
    spl9_9 ),
    inference(avatar_split_clause,[],[f64,f140])).

fof(f64,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f138,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f65,f135])).

fof(f65,plain,(
    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f66,f130])).

fof(f66,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f67,f125])).

fof(f67,plain,(
    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    spl9_5 ),
    inference(avatar_split_clause,[],[f68,f120])).

fof(f68,plain,(
    m1_subset_1(sK7,u1_struct_0(sK5)) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f69,f115])).

fof(f69,plain,(
    m1_subset_1(sK8,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f70,f110])).

fof(f70,plain,(
    sK7 = sK8 ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f71,f105])).

fof(f71,plain,(
    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f103,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f72,f100])).

fof(f72,plain,(
    ~ r1_tmap_1(sK5,sK3,sK6,sK7) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:37:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.45  % (19774)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.47  % (19781)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.47  % (19780)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.47  % (19765)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (19772)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.48  % (19773)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.48  % (19777)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (19779)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.50  % (19766)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.50  % (19778)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.50  % (19769)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.50  % (19767)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.50  % (19768)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.50  % (19771)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.50  % (19765)Refutation not found, incomplete strategy% (19765)------------------------------
% 0.19/0.50  % (19765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (19765)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (19765)Memory used [KB]: 6652
% 0.19/0.50  % (19765)Time elapsed: 0.096 s
% 0.19/0.50  % (19765)------------------------------
% 0.19/0.50  % (19765)------------------------------
% 0.19/0.51  % (19776)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.51  % (19770)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (19775)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.51  % (19784)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.32/0.52  % (19783)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.32/0.52  % (19785)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.32/0.52  % (19782)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 2.64/0.74  % (19781)Refutation found. Thanks to Tanya!
% 2.64/0.74  % SZS status Theorem for theBenchmark
% 2.64/0.74  % SZS output start Proof for theBenchmark
% 2.64/0.74  fof(f4928,plain,(
% 2.64/0.74    $false),
% 2.64/0.74    inference(avatar_sat_refutation,[],[f103,f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f158,f163,f168,f173,f178,f183,f188,f193,f200,f206,f218,f244,f270,f275,f284,f289,f294,f316,f324,f363,f364,f367,f370,f378,f386,f396,f447,f454,f806,f1005,f1107,f1131,f4927])).
% 2.64/0.74  fof(f4927,plain,(
% 2.64/0.74    spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_39 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_113 | ~spl9_125),
% 2.64/0.74    inference(avatar_contradiction_clause,[],[f4926])).
% 2.64/0.74  fof(f4926,plain,(
% 2.64/0.74    $false | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_39 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_113 | ~spl9_125)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4925,f313])).
% 2.64/0.74  fof(f313,plain,(
% 2.64/0.74    l1_pre_topc(sK4) | ~spl9_39),
% 2.64/0.74    inference(avatar_component_clause,[],[f312])).
% 2.64/0.74  fof(f312,plain,(
% 2.64/0.74    spl9_39 <=> l1_pre_topc(sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 2.64/0.74  fof(f4925,plain,(
% 2.64/0.74    ~l1_pre_topc(sK4) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_43 | ~spl9_47 | ~spl9_113 | ~spl9_125)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4924,f395])).
% 2.64/0.74  fof(f395,plain,(
% 2.64/0.74    m1_pre_topc(sK4,sK4) | ~spl9_43),
% 2.64/0.74    inference(avatar_component_clause,[],[f393])).
% 2.64/0.74  fof(f393,plain,(
% 2.64/0.74    spl9_43 <=> m1_pre_topc(sK4,sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_43])])).
% 2.64/0.74  fof(f4924,plain,(
% 2.64/0.74    ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_47 | ~spl9_113 | ~spl9_125)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4923,f162])).
% 2.64/0.74  fof(f162,plain,(
% 2.64/0.74    ~v2_struct_0(sK4) | spl9_13),
% 2.64/0.74    inference(avatar_component_clause,[],[f160])).
% 2.64/0.74  fof(f160,plain,(
% 2.64/0.74    spl9_13 <=> v2_struct_0(sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 2.64/0.74  fof(f4923,plain,(
% 2.64/0.74    v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_47 | ~spl9_113 | ~spl9_125)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4911,f435])).
% 2.64/0.74  fof(f435,plain,(
% 2.64/0.74    v2_pre_topc(sK4) | ~spl9_47),
% 2.64/0.74    inference(avatar_component_clause,[],[f433])).
% 2.64/0.74  fof(f433,plain,(
% 2.64/0.74    spl9_47 <=> v2_pre_topc(sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_47])])).
% 2.64/0.74  fof(f4911,plain,(
% 2.64/0.74    ~v2_pre_topc(sK4) | v2_struct_0(sK4) | ~m1_pre_topc(sK4,sK4) | ~l1_pre_topc(sK4) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113 | ~spl9_125)),
% 2.64/0.74    inference(resolution,[],[f4828,f1129])).
% 2.64/0.74  fof(f1129,plain,(
% 2.64/0.74    v1_tsep_1(sK4,sK4) | ~spl9_125),
% 2.64/0.74    inference(avatar_component_clause,[],[f1127])).
% 2.64/0.74  fof(f1127,plain,(
% 2.64/0.74    spl9_125 <=> v1_tsep_1(sK4,sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_125])])).
% 2.64/0.74  fof(f4828,plain,(
% 2.64/0.74    ( ! [X0] : (~v1_tsep_1(sK4,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4827,f306])).
% 2.64/0.74  fof(f306,plain,(
% 2.64/0.74    v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~spl9_38),
% 2.64/0.74    inference(avatar_component_clause,[],[f305])).
% 2.64/0.74  fof(f305,plain,(
% 2.64/0.74    spl9_38 <=> v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3))),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_38])])).
% 2.64/0.74  fof(f4827,plain,(
% 2.64/0.74    ( ! [X0] : (~v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4826,f385])).
% 2.64/0.74  fof(f385,plain,(
% 2.64/0.74    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_42),
% 2.64/0.74    inference(avatar_component_clause,[],[f383])).
% 2.64/0.74  fof(f383,plain,(
% 2.64/0.74    spl9_42 <=> u1_struct_0(sK5) = k2_struct_0(sK5)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_42])])).
% 2.64/0.74  fof(f4826,plain,(
% 2.64/0.74    ( ! [X0] : (~v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4825,f243])).
% 2.64/0.74  fof(f243,plain,(
% 2.64/0.74    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_26),
% 2.64/0.74    inference(avatar_component_clause,[],[f241])).
% 2.64/0.74  fof(f241,plain,(
% 2.64/0.74    spl9_26 <=> u1_struct_0(sK3) = k2_struct_0(sK3)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 2.64/0.74  fof(f4825,plain,(
% 2.64/0.74    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4824,f301])).
% 2.64/0.74  fof(f301,plain,(
% 2.64/0.74    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~spl9_37),
% 2.64/0.74    inference(avatar_component_clause,[],[f300])).
% 2.64/0.74  fof(f300,plain,(
% 2.64/0.74    spl9_37 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3))))),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 2.64/0.74  fof(f4824,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4823,f385])).
% 2.64/0.74  fof(f4823,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4822,f243])).
% 2.64/0.74  fof(f4822,plain,(
% 2.64/0.74    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_36 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4821,f293])).
% 2.64/0.74  fof(f293,plain,(
% 2.64/0.74    m1_subset_1(sK7,k2_struct_0(sK5)) | ~spl9_36),
% 2.64/0.74    inference(avatar_component_clause,[],[f291])).
% 2.64/0.74  fof(f291,plain,(
% 2.64/0.74    spl9_36 <=> m1_subset_1(sK7,k2_struct_0(sK5))),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_36])])).
% 2.64/0.74  fof(f4821,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK7,k2_struct_0(sK5)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4820,f385])).
% 2.64/0.74  fof(f4820,plain,(
% 2.64/0.74    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_32 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4819,f274])).
% 2.64/0.74  fof(f274,plain,(
% 2.64/0.74    m1_subset_1(sK7,k2_struct_0(sK4)) | ~spl9_32),
% 2.64/0.74    inference(avatar_component_clause,[],[f272])).
% 2.64/0.74  fof(f272,plain,(
% 2.64/0.74    spl9_32 <=> m1_subset_1(sK7,k2_struct_0(sK4))),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_32])])).
% 2.64/0.74  fof(f4819,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK7,k2_struct_0(sK4)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4818,f377])).
% 2.64/0.74  fof(f377,plain,(
% 2.64/0.74    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_41),
% 2.64/0.74    inference(avatar_component_clause,[],[f375])).
% 2.64/0.74  fof(f375,plain,(
% 2.64/0.74    spl9_41 <=> u1_struct_0(sK4) = k2_struct_0(sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_41])])).
% 2.64/0.74  fof(f4818,plain,(
% 2.64/0.74    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_31 | ~spl9_37 | ~spl9_38 | ~spl9_41 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4817,f633])).
% 2.64/0.74  fof(f633,plain,(
% 2.64/0.74    ( ! [X4] : (m1_pre_topc(sK5,X4) | ~m1_pre_topc(sK4,X4) | ~l1_pre_topc(X4)) ) | (~spl9_31 | ~spl9_41)),
% 2.64/0.74    inference(forward_demodulation,[],[f596,f269])).
% 2.64/0.74  fof(f269,plain,(
% 2.64/0.74    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~spl9_31),
% 2.64/0.74    inference(avatar_component_clause,[],[f267])).
% 2.64/0.74  fof(f267,plain,(
% 2.64/0.74    spl9_31 <=> sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_31])])).
% 2.64/0.74  fof(f596,plain,(
% 2.64/0.74    ( ! [X4] : (m1_pre_topc(g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)),X4) | ~m1_pre_topc(sK4,X4) | ~l1_pre_topc(X4)) ) | ~spl9_41),
% 2.64/0.74    inference(superposition,[],[f81,f377])).
% 2.64/0.74  fof(f81,plain,(
% 2.64/0.74    ( ! [X0,X1] : (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f24])).
% 2.64/0.74  fof(f24,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : ((m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.64/0.74    inference(ennf_transformation,[],[f8])).
% 2.64/0.74  fof(f8,axiom,(
% 2.64/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0) & v1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).
% 2.64/0.74  fof(f4817,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4816,f177])).
% 2.64/0.74  fof(f177,plain,(
% 2.64/0.74    ~v2_struct_0(sK3) | spl9_16),
% 2.64/0.74    inference(avatar_component_clause,[],[f175])).
% 2.64/0.74  fof(f175,plain,(
% 2.64/0.74    spl9_16 <=> v2_struct_0(sK3)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.64/0.74  fof(f4816,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4815,f172])).
% 2.64/0.74  fof(f172,plain,(
% 2.64/0.74    v2_pre_topc(sK3) | ~spl9_15),
% 2.64/0.74    inference(avatar_component_clause,[],[f170])).
% 2.64/0.74  fof(f170,plain,(
% 2.64/0.74    spl9_15 <=> v2_pre_topc(sK3)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.64/0.74  fof(f4815,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4814,f167])).
% 2.64/0.74  fof(f167,plain,(
% 2.64/0.74    l1_pre_topc(sK3) | ~spl9_14),
% 2.64/0.74    inference(avatar_component_clause,[],[f165])).
% 2.64/0.74  fof(f165,plain,(
% 2.64/0.74    spl9_14 <=> l1_pre_topc(sK3)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 2.64/0.74  fof(f4814,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | spl9_13 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4813,f162])).
% 2.64/0.74  fof(f4813,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | spl9_11 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4812,f152])).
% 2.64/0.74  fof(f152,plain,(
% 2.64/0.74    ~v2_struct_0(sK5) | spl9_11),
% 2.64/0.74    inference(avatar_component_clause,[],[f150])).
% 2.64/0.74  fof(f150,plain,(
% 2.64/0.74    spl9_11 <=> v2_struct_0(sK5)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 2.64/0.74  fof(f4812,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4811,f142])).
% 2.64/0.74  fof(f142,plain,(
% 2.64/0.74    v1_funct_1(sK6) | ~spl9_9),
% 2.64/0.74    inference(avatar_component_clause,[],[f140])).
% 2.64/0.74  fof(f140,plain,(
% 2.64/0.74    spl9_9 <=> v1_funct_1(sK6)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 2.64/0.74  fof(f4811,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4810,f1004])).
% 2.64/0.74  fof(f1004,plain,(
% 2.64/0.74    m1_pre_topc(sK4,sK5) | ~spl9_113),
% 2.64/0.74    inference(avatar_component_clause,[],[f1002])).
% 2.64/0.74  fof(f1002,plain,(
% 2.64/0.74    spl9_113 <=> m1_pre_topc(sK4,sK5)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_113])])).
% 2.64/0.74  fof(f4810,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (spl9_1 | ~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4799,f102])).
% 2.64/0.74  fof(f102,plain,(
% 2.64/0.74    ~r1_tmap_1(sK5,sK3,sK6,sK7) | spl9_1),
% 2.64/0.74    inference(avatar_component_clause,[],[f100])).
% 2.64/0.74  fof(f100,plain,(
% 2.64/0.74    spl9_1 <=> r1_tmap_1(sK5,sK3,sK6,sK7)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.64/0.74  fof(f4799,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(duplicate_literal_removal,[],[f4786])).
% 2.64/0.74  fof(f4786,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | r1_tmap_1(sK5,sK3,sK6,sK7) | ~m1_subset_1(sK7,u1_struct_0(sK4)) | ~m1_subset_1(sK7,u1_struct_0(sK5)) | ~m1_pre_topc(sK4,sK5) | ~m1_pre_topc(sK4,X0) | ~v1_tsep_1(sK4,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK5) | v2_struct_0(sK4) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(resolution,[],[f4320,f98])).
% 2.64/0.74  fof(f98,plain,(
% 2.64/0.74    ( ! [X6,X4,X2,X0,X3,X1] : (~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | r1_tmap_1(X3,X0,X4,X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.74    inference(duplicate_literal_removal,[],[f94])).
% 2.64/0.74  fof(f94,plain,(
% 2.64/0.74    ( ! [X6,X4,X2,X0,X3,X1] : (r1_tmap_1(X3,X0,X4,X6) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X6,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.74    inference(equality_resolution,[],[f84])).
% 2.64/0.74  fof(f84,plain,(
% 2.64/0.74    ( ! [X6,X4,X2,X0,X5,X3,X1] : (r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f49])).
% 2.64/0.74  fof(f49,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) | ~r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) & (r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6) | ~r1_tmap_1(X3,X0,X4,X5))) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.74    inference(nnf_transformation,[],[f28])).
% 2.64/0.74  fof(f28,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6 | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X1) | v2_struct_0(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.74    inference(flattening,[],[f27])).
% 2.64/0.74  fof(f27,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((! [X5] : (! [X6] : (((r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)) | X5 != X6) | ~m1_subset_1(X6,u1_struct_0(X2))) | ~m1_subset_1(X5,u1_struct_0(X3))) | (~m1_pre_topc(X2,X3) | ~m1_pre_topc(X2,X1) | ~v1_tsep_1(X2,X1))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) | ~v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) | ~v1_funct_1(X4))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X1) | v2_struct_0(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.74    inference(ennf_transformation,[],[f13])).
% 2.64/0.74  fof(f13,axiom,(
% 2.64/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X1) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X0)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X0)) & v1_funct_1(X4)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X2,X1) & v1_tsep_1(X2,X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => (X5 = X6 => (r1_tmap_1(X3,X0,X4,X5) <=> r1_tmap_1(X2,X0,k3_tmap_1(X1,X0,X3,X2,X4),X6)))))))))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).
% 2.64/0.74  fof(f4320,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_38 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4319,f306])).
% 2.64/0.74  fof(f4319,plain,(
% 2.64/0.74    ( ! [X0] : (~v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4318,f385])).
% 2.64/0.74  fof(f4318,plain,(
% 2.64/0.74    ( ! [X0] : (~v1_funct_2(sK6,u1_struct_0(sK5),k2_struct_0(sK3)) | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4317,f243])).
% 2.64/0.74  fof(f4317,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_37 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4316,f301])).
% 2.64/0.74  fof(f4316,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_42 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4315,f385])).
% 2.64/0.74  fof(f4315,plain,(
% 2.64/0.74    ( ! [X0] : (~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),k2_struct_0(sK3)))) | r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_26 | ~spl9_113)),
% 2.64/0.74    inference(forward_demodulation,[],[f4314,f243])).
% 2.64/0.74  fof(f4314,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | spl9_19 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4313,f192])).
% 2.64/0.74  fof(f192,plain,(
% 2.64/0.74    ~v2_struct_0(sK2) | spl9_19),
% 2.64/0.74    inference(avatar_component_clause,[],[f190])).
% 2.64/0.74  fof(f190,plain,(
% 2.64/0.74    spl9_19 <=> v2_struct_0(sK2)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 2.64/0.74  fof(f4313,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_18 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4312,f187])).
% 2.64/0.74  fof(f187,plain,(
% 2.64/0.74    v2_pre_topc(sK2) | ~spl9_18),
% 2.64/0.74    inference(avatar_component_clause,[],[f185])).
% 2.64/0.74  fof(f185,plain,(
% 2.64/0.74    spl9_18 <=> v2_pre_topc(sK2)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).
% 2.64/0.74  fof(f4312,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_17 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4311,f182])).
% 2.64/0.74  fof(f182,plain,(
% 2.64/0.74    l1_pre_topc(sK2) | ~spl9_17),
% 2.64/0.74    inference(avatar_component_clause,[],[f180])).
% 2.64/0.74  fof(f180,plain,(
% 2.64/0.74    spl9_17 <=> l1_pre_topc(sK2)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.64/0.74  fof(f4311,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_10 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4310,f147])).
% 2.64/0.74  fof(f147,plain,(
% 2.64/0.74    m1_pre_topc(sK5,sK2) | ~spl9_10),
% 2.64/0.74    inference(avatar_component_clause,[],[f145])).
% 2.64/0.74  fof(f145,plain,(
% 2.64/0.74    spl9_10 <=> m1_pre_topc(sK5,sK2)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 2.64/0.74  fof(f4310,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_14 | ~spl9_15 | spl9_16 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4309,f177])).
% 2.64/0.74  fof(f4309,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_14 | ~spl9_15 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4308,f172])).
% 2.64/0.74  fof(f4308,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_14 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4307,f167])).
% 2.64/0.74  fof(f4307,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_9 | ~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4306,f142])).
% 2.64/0.74  fof(f4306,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | (~spl9_21 | ~spl9_113)),
% 2.64/0.74    inference(subsumption_resolution,[],[f4267,f1004])).
% 2.64/0.74  fof(f4267,plain,(
% 2.64/0.74    ( ! [X0] : (r1_tmap_1(sK4,sK3,k3_tmap_1(X0,sK3,sK5,sK4,sK6),sK7) | ~m1_pre_topc(sK4,sK5) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~v1_funct_1(sK6) | ~m1_pre_topc(sK5,X0) | ~l1_pre_topc(sK3) | ~v2_pre_topc(sK3) | v2_struct_0(sK3) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(sK5,sK2) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | v2_struct_0(sK2)) ) | ~spl9_21),
% 2.64/0.74    inference(superposition,[],[f205,f1192])).
% 2.64/0.74  fof(f1192,plain,(
% 2.64/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.64/0.74    inference(subsumption_resolution,[],[f1191,f87])).
% 2.64/0.74  fof(f87,plain,(
% 2.64/0.74    ( ! [X2,X0,X1] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f34])).
% 2.64/0.74  fof(f34,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.74    inference(flattening,[],[f33])).
% 2.64/0.74  fof(f33,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X2,X0) | ~m1_pre_topc(X2,X1)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.74    inference(ennf_transformation,[],[f12])).
% 2.64/0.74  fof(f12,axiom,(
% 2.64/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X1) => m1_pre_topc(X2,X0))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).
% 2.64/0.74  fof(f1191,plain,(
% 2.64/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.64/0.74    inference(subsumption_resolution,[],[f1178,f87])).
% 2.64/0.74  fof(f1178,plain,(
% 2.64/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.64/0.74    inference(duplicate_literal_removal,[],[f1177])).
% 2.64/0.74  fof(f1177,plain,(
% 2.64/0.74    ( ! [X4,X2,X0,X5,X3,X1] : (k3_tmap_1(X4,X1,X0,X3,X2) = k3_tmap_1(X5,X1,X0,X3,X2) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,X5) | ~m1_pre_topc(X0,X5) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X5) | ~v2_pre_topc(X5) | v2_struct_0(X5) | ~m1_pre_topc(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X0,X4) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | v2_struct_0(X4)) )),
% 2.64/0.74    inference(superposition,[],[f82,f82])).
% 2.64/0.74  fof(f82,plain,(
% 2.64/0.74    ( ! [X4,X2,X0,X3,X1] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4) | ~m1_pre_topc(X3,X0) | ~m1_pre_topc(X2,X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f26])).
% 2.64/0.74  fof(f26,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4)) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.64/0.74    inference(flattening,[],[f25])).
% 2.64/0.74  fof(f25,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3)) | ~m1_pre_topc(X3,X2)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) | ~v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) | ~v1_funct_1(X4))) | ~m1_pre_topc(X3,X0)) | ~m1_pre_topc(X2,X0)) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.64/0.74    inference(ennf_transformation,[],[f7])).
% 2.64/0.74  fof(f7,axiom,(
% 2.64/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_pre_topc(X2,X0) => ! [X3] : (m1_pre_topc(X3,X0) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X2),u1_struct_0(X1)) & v1_funct_1(X4)) => (m1_pre_topc(X3,X2) => k3_tmap_1(X0,X1,X2,X3,X4) = k2_partfun1(u1_struct_0(X2),u1_struct_0(X1),X4,u1_struct_0(X3))))))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).
% 2.64/0.74  fof(f205,plain,(
% 2.64/0.74    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | ~spl9_21),
% 2.64/0.74    inference(avatar_component_clause,[],[f203])).
% 2.64/0.74  fof(f203,plain,(
% 2.64/0.74    spl9_21 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).
% 2.64/0.74  fof(f1131,plain,(
% 2.64/0.74    spl9_125 | ~spl9_124),
% 2.64/0.74    inference(avatar_split_clause,[],[f1125,f1102,f1127])).
% 2.64/0.74  fof(f1102,plain,(
% 2.64/0.74    spl9_124 <=> sP0(sK4,sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_124])])).
% 2.64/0.74  fof(f1125,plain,(
% 2.64/0.74    v1_tsep_1(sK4,sK4) | ~spl9_124),
% 2.64/0.74    inference(resolution,[],[f1104,f90])).
% 2.64/0.74  fof(f90,plain,(
% 2.64/0.74    ( ! [X0,X1] : (~sP0(X0,X1) | v1_tsep_1(X1,X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f53])).
% 2.64/0.74  fof(f53,plain,(
% 2.64/0.74    ! [X0,X1] : ((sP0(X0,X1) | ~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0)) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 2.64/0.74    inference(flattening,[],[f52])).
% 2.64/0.74  fof(f52,plain,(
% 2.64/0.74    ! [X0,X1] : ((sP0(X0,X1) | (~m1_pre_topc(X1,X0) | ~v1_tsep_1(X1,X0))) & ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) | ~sP0(X0,X1)))),
% 2.64/0.74    inference(nnf_transformation,[],[f37])).
% 2.64/0.74  fof(f37,plain,(
% 2.64/0.74    ! [X0,X1] : (sP0(X0,X1) <=> (m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)))),
% 2.64/0.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.64/0.74  fof(f1104,plain,(
% 2.64/0.74    sP0(sK4,sK4) | ~spl9_124),
% 2.64/0.74    inference(avatar_component_clause,[],[f1102])).
% 2.64/0.74  fof(f1107,plain,(
% 2.64/0.74    spl9_124 | ~spl9_49 | ~spl9_91),
% 2.64/0.74    inference(avatar_split_clause,[],[f1106,f803,f451,f1102])).
% 2.64/0.74  fof(f451,plain,(
% 2.64/0.74    spl9_49 <=> v3_pre_topc(k2_struct_0(sK4),sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_49])])).
% 2.64/0.74  fof(f803,plain,(
% 2.64/0.74    spl9_91 <=> sP1(sK4,k2_struct_0(sK4),sK4)),
% 2.64/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_91])])).
% 2.64/0.74  fof(f1106,plain,(
% 2.64/0.74    sP0(sK4,sK4) | (~spl9_49 | ~spl9_91)),
% 2.64/0.74    inference(subsumption_resolution,[],[f1099,f453])).
% 2.64/0.74  fof(f453,plain,(
% 2.64/0.74    v3_pre_topc(k2_struct_0(sK4),sK4) | ~spl9_49),
% 2.64/0.74    inference(avatar_component_clause,[],[f451])).
% 2.64/0.74  fof(f1099,plain,(
% 2.64/0.74    ~v3_pre_topc(k2_struct_0(sK4),sK4) | sP0(sK4,sK4) | ~spl9_91),
% 2.64/0.74    inference(resolution,[],[f805,f89])).
% 2.64/0.74  fof(f89,plain,(
% 2.64/0.74    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~v3_pre_topc(X1,X0) | sP0(X0,X2)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f51])).
% 2.64/0.74  fof(f51,plain,(
% 2.64/0.74    ! [X0,X1,X2] : (((sP0(X0,X2) | ~v3_pre_topc(X1,X0)) & (v3_pre_topc(X1,X0) | ~sP0(X0,X2))) | ~sP1(X0,X1,X2))),
% 2.64/0.74    inference(rectify,[],[f50])).
% 2.64/0.74  fof(f50,plain,(
% 2.64/0.74    ! [X0,X2,X1] : (((sP0(X0,X1) | ~v3_pre_topc(X2,X0)) & (v3_pre_topc(X2,X0) | ~sP0(X0,X1))) | ~sP1(X0,X2,X1))),
% 2.64/0.74    inference(nnf_transformation,[],[f38])).
% 2.64/0.74  fof(f38,plain,(
% 2.64/0.74    ! [X0,X2,X1] : ((sP0(X0,X1) <=> v3_pre_topc(X2,X0)) | ~sP1(X0,X2,X1))),
% 2.64/0.74    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.64/0.74  fof(f805,plain,(
% 2.64/0.74    sP1(sK4,k2_struct_0(sK4),sK4) | ~spl9_91),
% 2.64/0.74    inference(avatar_component_clause,[],[f803])).
% 2.64/0.74  fof(f1005,plain,(
% 2.64/0.74    spl9_113 | ~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43),
% 2.64/0.74    inference(avatar_split_clause,[],[f1000,f393,f375,f312,f267,f1002])).
% 2.64/0.74  fof(f1000,plain,(
% 2.64/0.74    m1_pre_topc(sK4,sK5) | (~spl9_31 | ~spl9_39 | ~spl9_41 | ~spl9_43)),
% 2.64/0.74    inference(forward_demodulation,[],[f999,f269])).
% 2.64/0.74  fof(f999,plain,(
% 2.64/0.74    m1_pre_topc(sK4,g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4))) | (~spl9_39 | ~spl9_41 | ~spl9_43)),
% 2.64/0.74    inference(forward_demodulation,[],[f981,f377])).
% 2.64/0.74  fof(f981,plain,(
% 2.64/0.74    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl9_39 | ~spl9_43)),
% 2.64/0.74    inference(unit_resulting_resolution,[],[f313,f313,f395,f76])).
% 2.64/0.74  fof(f76,plain,(
% 2.64/0.74    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f48])).
% 2.64/0.74  fof(f48,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.74    inference(nnf_transformation,[],[f21])).
% 2.64/0.74  fof(f21,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.64/0.74    inference(ennf_transformation,[],[f5])).
% 2.64/0.74  fof(f5,axiom,(
% 2.64/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 2.64/0.74  fof(f806,plain,(
% 2.64/0.74    spl9_91 | ~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47),
% 2.64/0.74    inference(avatar_split_clause,[],[f801,f433,f393,f375,f312,f803])).
% 2.64/0.74  fof(f801,plain,(
% 2.64/0.74    sP1(sK4,k2_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_41 | ~spl9_43 | ~spl9_47)),
% 2.64/0.74    inference(forward_demodulation,[],[f779,f377])).
% 2.64/0.74  fof(f779,plain,(
% 2.64/0.74    sP1(sK4,u1_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_43 | ~spl9_47)),
% 2.64/0.74    inference(unit_resulting_resolution,[],[f435,f313,f395,f194])).
% 2.64/0.74  fof(f194,plain,(
% 2.64/0.74    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.74    inference(subsumption_resolution,[],[f96,f79])).
% 2.64/0.74  fof(f79,plain,(
% 2.64/0.74    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f23])).
% 2.64/0.74  fof(f23,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.64/0.74    inference(ennf_transformation,[],[f10])).
% 2.64/0.74  fof(f10,axiom,(
% 2.64/0.74    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 2.64/0.74  fof(f96,plain,(
% 2.64/0.74    ( ! [X0,X1] : (sP1(X0,u1_struct_0(X1),X1) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.74    inference(equality_resolution,[],[f93])).
% 2.64/0.74  fof(f93,plain,(
% 2.64/0.74    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.74    inference(cnf_transformation,[],[f39])).
% 2.64/0.74  fof(f39,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (sP1(X0,X2,X1) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.74    inference(definition_folding,[],[f36,f38,f37])).
% 2.64/0.74  fof(f36,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.74    inference(flattening,[],[f35])).
% 2.64/0.74  fof(f35,plain,(
% 2.64/0.74    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.74    inference(ennf_transformation,[],[f9])).
% 2.64/0.74  fof(f9,axiom,(
% 2.64/0.74    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> v3_pre_topc(X2,X0))))))),
% 2.64/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).
% 2.64/0.75  fof(f454,plain,(
% 2.64/0.75    spl9_49 | ~spl9_39 | ~spl9_47),
% 2.64/0.75    inference(avatar_split_clause,[],[f449,f433,f312,f451])).
% 2.64/0.75  fof(f449,plain,(
% 2.64/0.75    v3_pre_topc(k2_struct_0(sK4),sK4) | (~spl9_39 | ~spl9_47)),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f313,f435,f85])).
% 2.64/0.75  fof(f85,plain,(
% 2.64/0.75    ( ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f30])).
% 2.64/0.75  fof(f30,plain,(
% 2.64/0.75    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.75    inference(flattening,[],[f29])).
% 2.64/0.75  fof(f29,plain,(
% 2.64/0.75    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.75    inference(ennf_transformation,[],[f6])).
% 2.64/0.75  fof(f6,axiom,(
% 2.64/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 2.64/0.75  fof(f447,plain,(
% 2.64/0.75    spl9_47 | ~spl9_12 | ~spl9_17 | ~spl9_18),
% 2.64/0.75    inference(avatar_split_clause,[],[f446,f185,f180,f155,f433])).
% 2.64/0.75  fof(f155,plain,(
% 2.64/0.75    spl9_12 <=> m1_pre_topc(sK4,sK2)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 2.64/0.75  fof(f446,plain,(
% 2.64/0.75    v2_pre_topc(sK4) | (~spl9_12 | ~spl9_17 | ~spl9_18)),
% 2.64/0.75    inference(subsumption_resolution,[],[f445,f187])).
% 2.64/0.75  fof(f445,plain,(
% 2.64/0.75    v2_pre_topc(sK4) | ~v2_pre_topc(sK2) | (~spl9_12 | ~spl9_17)),
% 2.64/0.75    inference(subsumption_resolution,[],[f426,f182])).
% 2.64/0.75  fof(f426,plain,(
% 2.64/0.75    v2_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~spl9_12),
% 2.64/0.75    inference(resolution,[],[f86,f157])).
% 2.64/0.75  fof(f157,plain,(
% 2.64/0.75    m1_pre_topc(sK4,sK2) | ~spl9_12),
% 2.64/0.75    inference(avatar_component_clause,[],[f155])).
% 2.64/0.75  fof(f86,plain,(
% 2.64/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f32])).
% 2.64/0.75  fof(f32,plain,(
% 2.64/0.75    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.64/0.75    inference(flattening,[],[f31])).
% 2.64/0.75  fof(f31,plain,(
% 2.64/0.75    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.64/0.75    inference(ennf_transformation,[],[f1])).
% 2.64/0.75  fof(f1,axiom,(
% 2.64/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 2.64/0.75  fof(f396,plain,(
% 2.64/0.75    spl9_43 | ~spl9_39),
% 2.64/0.75    inference(avatar_split_clause,[],[f390,f312,f393])).
% 2.64/0.75  fof(f390,plain,(
% 2.64/0.75    m1_pre_topc(sK4,sK4) | ~spl9_39),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f313,f75])).
% 2.64/0.75  fof(f75,plain,(
% 2.64/0.75    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f20])).
% 2.64/0.75  fof(f20,plain,(
% 2.64/0.75    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 2.64/0.75    inference(ennf_transformation,[],[f11])).
% 2.64/0.75  fof(f11,axiom,(
% 2.64/0.75    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 2.64/0.75  fof(f386,plain,(
% 2.64/0.75    spl9_42 | ~spl9_33),
% 2.64/0.75    inference(avatar_split_clause,[],[f381,f277,f383])).
% 2.64/0.75  fof(f277,plain,(
% 2.64/0.75    spl9_33 <=> l1_struct_0(sK5)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_33])])).
% 2.64/0.75  fof(f381,plain,(
% 2.64/0.75    u1_struct_0(sK5) = k2_struct_0(sK5) | ~spl9_33),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f278,f73])).
% 2.64/0.75  fof(f73,plain,(
% 2.64/0.75    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f18])).
% 2.64/0.75  fof(f18,plain,(
% 2.64/0.75    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.64/0.75    inference(ennf_transformation,[],[f2])).
% 2.64/0.75  fof(f2,axiom,(
% 2.64/0.75    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.64/0.75  fof(f278,plain,(
% 2.64/0.75    l1_struct_0(sK5) | ~spl9_33),
% 2.64/0.75    inference(avatar_component_clause,[],[f277])).
% 2.64/0.75  fof(f378,plain,(
% 2.64/0.75    spl9_41 | ~spl9_30),
% 2.64/0.75    inference(avatar_split_clause,[],[f373,f263,f375])).
% 2.64/0.75  fof(f263,plain,(
% 2.64/0.75    spl9_30 <=> l1_struct_0(sK4)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).
% 2.64/0.75  fof(f373,plain,(
% 2.64/0.75    u1_struct_0(sK4) = k2_struct_0(sK4) | ~spl9_30),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f264,f73])).
% 2.64/0.75  fof(f264,plain,(
% 2.64/0.75    l1_struct_0(sK4) | ~spl9_30),
% 2.64/0.75    inference(avatar_component_clause,[],[f263])).
% 2.64/0.75  fof(f370,plain,(
% 2.64/0.75    spl9_40 | ~spl9_10 | ~spl9_17),
% 2.64/0.75    inference(avatar_split_clause,[],[f329,f180,f145,f320])).
% 2.64/0.75  fof(f320,plain,(
% 2.64/0.75    spl9_40 <=> l1_pre_topc(sK5)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_40])])).
% 2.64/0.75  fof(f329,plain,(
% 2.64/0.75    l1_pre_topc(sK5) | (~spl9_10 | ~spl9_17)),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f182,f147,f78])).
% 2.64/0.75  fof(f78,plain,(
% 2.64/0.75    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f22])).
% 2.64/0.75  fof(f22,plain,(
% 2.64/0.75    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.64/0.75    inference(ennf_transformation,[],[f4])).
% 2.64/0.75  fof(f4,axiom,(
% 2.64/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.64/0.75  fof(f367,plain,(
% 2.64/0.75    spl9_39 | ~spl9_12 | ~spl9_17),
% 2.64/0.75    inference(avatar_split_clause,[],[f332,f180,f155,f312])).
% 2.64/0.75  fof(f332,plain,(
% 2.64/0.75    l1_pre_topc(sK4) | (~spl9_12 | ~spl9_17)),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f182,f157,f78])).
% 2.64/0.75  fof(f364,plain,(
% 2.64/0.75    u1_struct_0(sK3) != k2_struct_0(sK3) | v1_funct_2(sK6,k2_struct_0(sK5),k2_struct_0(sK3)) | ~v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 2.64/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.75  fof(f363,plain,(
% 2.64/0.75    u1_struct_0(sK3) != k2_struct_0(sK3) | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),k2_struct_0(sK3)))) | ~m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 2.64/0.75    introduced(theory_tautology_sat_conflict,[])).
% 2.64/0.75  fof(f324,plain,(
% 2.64/0.75    ~spl9_40 | spl9_33),
% 2.64/0.75    inference(avatar_split_clause,[],[f318,f277,f320])).
% 2.64/0.75  fof(f318,plain,(
% 2.64/0.75    ~l1_pre_topc(sK5) | spl9_33),
% 2.64/0.75    inference(resolution,[],[f279,f74])).
% 2.64/0.75  fof(f74,plain,(
% 2.64/0.75    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 2.64/0.75    inference(cnf_transformation,[],[f19])).
% 2.64/0.75  fof(f19,plain,(
% 2.64/0.75    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.64/0.75    inference(ennf_transformation,[],[f3])).
% 2.64/0.75  fof(f3,axiom,(
% 2.64/0.75    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.64/0.75  fof(f279,plain,(
% 2.64/0.75    ~l1_struct_0(sK5) | spl9_33),
% 2.64/0.75    inference(avatar_component_clause,[],[f277])).
% 2.64/0.75  fof(f316,plain,(
% 2.64/0.75    ~spl9_39 | spl9_30),
% 2.64/0.75    inference(avatar_split_clause,[],[f310,f263,f312])).
% 2.64/0.75  fof(f310,plain,(
% 2.64/0.75    ~l1_pre_topc(sK4) | spl9_30),
% 2.64/0.75    inference(resolution,[],[f265,f74])).
% 2.64/0.75  fof(f265,plain,(
% 2.64/0.75    ~l1_struct_0(sK4) | spl9_30),
% 2.64/0.75    inference(avatar_component_clause,[],[f263])).
% 2.64/0.75  fof(f294,plain,(
% 2.64/0.75    ~spl9_33 | spl9_36 | ~spl9_5),
% 2.64/0.75    inference(avatar_split_clause,[],[f239,f120,f291,f277])).
% 2.64/0.75  fof(f120,plain,(
% 2.64/0.75    spl9_5 <=> m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.64/0.75  fof(f239,plain,(
% 2.64/0.75    m1_subset_1(sK7,k2_struct_0(sK5)) | ~l1_struct_0(sK5) | ~spl9_5),
% 2.64/0.75    inference(superposition,[],[f122,f73])).
% 2.64/0.75  fof(f122,plain,(
% 2.64/0.75    m1_subset_1(sK7,u1_struct_0(sK5)) | ~spl9_5),
% 2.64/0.75    inference(avatar_component_clause,[],[f120])).
% 2.64/0.75  fof(f289,plain,(
% 2.64/0.75    ~spl9_33 | spl9_35 | ~spl9_8),
% 2.64/0.75    inference(avatar_split_clause,[],[f238,f135,f286,f277])).
% 2.64/0.75  fof(f286,plain,(
% 2.64/0.75    spl9_35 <=> v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_35])])).
% 2.64/0.75  fof(f135,plain,(
% 2.64/0.75    spl9_8 <=> v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 2.64/0.75  fof(f238,plain,(
% 2.64/0.75    v1_funct_2(sK6,k2_struct_0(sK5),u1_struct_0(sK3)) | ~l1_struct_0(sK5) | ~spl9_8),
% 2.64/0.75    inference(superposition,[],[f137,f73])).
% 2.64/0.75  fof(f137,plain,(
% 2.64/0.75    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) | ~spl9_8),
% 2.64/0.75    inference(avatar_component_clause,[],[f135])).
% 2.64/0.75  fof(f284,plain,(
% 2.64/0.75    ~spl9_33 | spl9_34 | ~spl9_7),
% 2.64/0.75    inference(avatar_split_clause,[],[f237,f130,f281,f277])).
% 2.64/0.75  fof(f281,plain,(
% 2.64/0.75    spl9_34 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3))))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_34])])).
% 2.64/0.75  fof(f130,plain,(
% 2.64/0.75    spl9_7 <=> m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 2.64/0.75  fof(f237,plain,(
% 2.64/0.75    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK5),u1_struct_0(sK3)))) | ~l1_struct_0(sK5) | ~spl9_7),
% 2.64/0.75    inference(superposition,[],[f132,f73])).
% 2.64/0.75  fof(f132,plain,(
% 2.64/0.75    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) | ~spl9_7),
% 2.64/0.75    inference(avatar_component_clause,[],[f130])).
% 2.64/0.75  fof(f275,plain,(
% 2.64/0.75    ~spl9_30 | spl9_32 | ~spl9_20),
% 2.64/0.75    inference(avatar_split_clause,[],[f236,f197,f272,f263])).
% 2.64/0.75  fof(f197,plain,(
% 2.64/0.75    spl9_20 <=> m1_subset_1(sK7,u1_struct_0(sK4))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 2.64/0.75  fof(f236,plain,(
% 2.64/0.75    m1_subset_1(sK7,k2_struct_0(sK4)) | ~l1_struct_0(sK4) | ~spl9_20),
% 2.64/0.75    inference(superposition,[],[f199,f73])).
% 2.64/0.75  fof(f199,plain,(
% 2.64/0.75    m1_subset_1(sK7,u1_struct_0(sK4)) | ~spl9_20),
% 2.64/0.75    inference(avatar_component_clause,[],[f197])).
% 2.64/0.75  fof(f270,plain,(
% 2.64/0.75    ~spl9_30 | spl9_31 | ~spl9_6),
% 2.64/0.75    inference(avatar_split_clause,[],[f235,f125,f267,f263])).
% 2.64/0.75  fof(f125,plain,(
% 2.64/0.75    spl9_6 <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 2.64/0.75  fof(f235,plain,(
% 2.64/0.75    sK5 = g1_pre_topc(k2_struct_0(sK4),u1_pre_topc(sK4)) | ~l1_struct_0(sK4) | ~spl9_6),
% 2.64/0.75    inference(superposition,[],[f127,f73])).
% 2.64/0.75  fof(f127,plain,(
% 2.64/0.75    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 | ~spl9_6),
% 2.64/0.75    inference(avatar_component_clause,[],[f125])).
% 2.64/0.75  fof(f244,plain,(
% 2.64/0.75    spl9_26 | ~spl9_23),
% 2.64/0.75    inference(avatar_split_clause,[],[f232,f215,f241])).
% 2.64/0.75  fof(f215,plain,(
% 2.64/0.75    spl9_23 <=> l1_struct_0(sK3)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 2.64/0.75  fof(f232,plain,(
% 2.64/0.75    u1_struct_0(sK3) = k2_struct_0(sK3) | ~spl9_23),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f217,f73])).
% 2.64/0.75  fof(f217,plain,(
% 2.64/0.75    l1_struct_0(sK3) | ~spl9_23),
% 2.64/0.75    inference(avatar_component_clause,[],[f215])).
% 2.64/0.75  fof(f218,plain,(
% 2.64/0.75    spl9_23 | ~spl9_14),
% 2.64/0.75    inference(avatar_split_clause,[],[f207,f165,f215])).
% 2.64/0.75  fof(f207,plain,(
% 2.64/0.75    l1_struct_0(sK3) | ~spl9_14),
% 2.64/0.75    inference(unit_resulting_resolution,[],[f167,f74])).
% 2.64/0.75  fof(f206,plain,(
% 2.64/0.75    spl9_21 | ~spl9_2 | ~spl9_3),
% 2.64/0.75    inference(avatar_split_clause,[],[f201,f110,f105,f203])).
% 2.64/0.75  fof(f105,plain,(
% 2.64/0.75    spl9_2 <=> r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.64/0.75  fof(f110,plain,(
% 2.64/0.75    spl9_3 <=> sK7 = sK8),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.64/0.75  fof(f201,plain,(
% 2.64/0.75    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK7) | (~spl9_2 | ~spl9_3)),
% 2.64/0.75    inference(forward_demodulation,[],[f107,f112])).
% 2.64/0.75  fof(f112,plain,(
% 2.64/0.75    sK7 = sK8 | ~spl9_3),
% 2.64/0.75    inference(avatar_component_clause,[],[f110])).
% 2.64/0.75  fof(f107,plain,(
% 2.64/0.75    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) | ~spl9_2),
% 2.64/0.75    inference(avatar_component_clause,[],[f105])).
% 2.64/0.75  fof(f200,plain,(
% 2.64/0.75    spl9_20 | ~spl9_3 | ~spl9_4),
% 2.64/0.75    inference(avatar_split_clause,[],[f195,f115,f110,f197])).
% 2.64/0.75  fof(f115,plain,(
% 2.64/0.75    spl9_4 <=> m1_subset_1(sK8,u1_struct_0(sK4))),
% 2.64/0.75    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 2.64/0.75  fof(f195,plain,(
% 2.64/0.75    m1_subset_1(sK7,u1_struct_0(sK4)) | (~spl9_3 | ~spl9_4)),
% 2.64/0.75    inference(backward_demodulation,[],[f117,f112])).
% 2.64/0.75  fof(f117,plain,(
% 2.64/0.75    m1_subset_1(sK8,u1_struct_0(sK4)) | ~spl9_4),
% 2.64/0.75    inference(avatar_component_clause,[],[f115])).
% 2.64/0.75  fof(f193,plain,(
% 2.64/0.75    ~spl9_19),
% 2.64/0.75    inference(avatar_split_clause,[],[f54,f190])).
% 2.64/0.75  fof(f54,plain,(
% 2.64/0.75    ~v2_struct_0(sK2)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f47,plain,(
% 2.64/0.75    ((((((~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 2.64/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6,sK7,sK8])],[f17,f46,f45,f44,f43,f42,f41,f40])).
% 2.64/0.75  fof(f40,plain,(
% 2.64/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f41,plain,(
% 2.64/0.75    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(sK2,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & l1_pre_topc(sK3) & v2_pre_topc(sK3) & ~v2_struct_0(sK3))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f42,plain,(
% 2.64/0.75    ? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(X2,sK3,k3_tmap_1(sK2,sK3,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f43,plain,(
% 2.64/0.75    ? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,X3,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f44,plain,(
% 2.64/0.75    ? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,X4,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(X4,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(X4)) => (? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) & g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5 & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3)))) & v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3)) & v1_funct_1(sK6))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f45,plain,(
% 2.64/0.75    ? [X5] : (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,X5) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(X5,u1_struct_0(sK5))) => (? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) & m1_subset_1(sK7,u1_struct_0(sK5)))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f46,plain,(
% 2.64/0.75    ? [X6] : (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),X6) & sK7 = X6 & m1_subset_1(X6,u1_struct_0(sK4))) => (~r1_tmap_1(sK5,sK3,sK6,sK7) & r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8) & sK7 = sK8 & m1_subset_1(sK8,u1_struct_0(sK4)))),
% 2.64/0.75    introduced(choice_axiom,[])).
% 2.64/0.75  fof(f17,plain,(
% 2.64/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : (? [X6] : (~r1_tmap_1(X3,X1,X4,X5) & r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6 & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.64/0.75    inference(flattening,[],[f16])).
% 2.64/0.75  fof(f16,plain,(
% 2.64/0.75    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : ((? [X5] : (? [X6] : ((~r1_tmap_1(X3,X1,X4,X5) & (r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6)) & m1_subset_1(X6,u1_struct_0(X2))) & m1_subset_1(X5,u1_struct_0(X3))) & g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.64/0.75    inference(ennf_transformation,[],[f15])).
% 2.64/0.75  fof(f15,negated_conjecture,(
% 2.64/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.64/0.75    inference(negated_conjecture,[],[f14])).
% 2.64/0.75  fof(f14,conjecture,(
% 2.64/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X3),u1_struct_0(X1)))) & v1_funct_2(X4,u1_struct_0(X3),u1_struct_0(X1)) & v1_funct_1(X4)) => (g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = X3 => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ! [X6] : (m1_subset_1(X6,u1_struct_0(X2)) => ((r1_tmap_1(X2,X1,k3_tmap_1(X0,X1,X3,X2,X4),X6) & X5 = X6) => r1_tmap_1(X3,X1,X4,X5))))))))))),
% 2.64/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).
% 2.64/0.75  fof(f188,plain,(
% 2.64/0.75    spl9_18),
% 2.64/0.75    inference(avatar_split_clause,[],[f55,f185])).
% 2.64/0.75  fof(f55,plain,(
% 2.64/0.75    v2_pre_topc(sK2)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f183,plain,(
% 2.64/0.75    spl9_17),
% 2.64/0.75    inference(avatar_split_clause,[],[f56,f180])).
% 2.64/0.75  fof(f56,plain,(
% 2.64/0.75    l1_pre_topc(sK2)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f178,plain,(
% 2.64/0.75    ~spl9_16),
% 2.64/0.75    inference(avatar_split_clause,[],[f57,f175])).
% 2.64/0.75  fof(f57,plain,(
% 2.64/0.75    ~v2_struct_0(sK3)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f173,plain,(
% 2.64/0.75    spl9_15),
% 2.64/0.75    inference(avatar_split_clause,[],[f58,f170])).
% 2.64/0.75  fof(f58,plain,(
% 2.64/0.75    v2_pre_topc(sK3)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f168,plain,(
% 2.64/0.75    spl9_14),
% 2.64/0.75    inference(avatar_split_clause,[],[f59,f165])).
% 2.64/0.75  fof(f59,plain,(
% 2.64/0.75    l1_pre_topc(sK3)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f163,plain,(
% 2.64/0.75    ~spl9_13),
% 2.64/0.75    inference(avatar_split_clause,[],[f60,f160])).
% 2.64/0.75  fof(f60,plain,(
% 2.64/0.75    ~v2_struct_0(sK4)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f158,plain,(
% 2.64/0.75    spl9_12),
% 2.64/0.75    inference(avatar_split_clause,[],[f61,f155])).
% 2.64/0.75  fof(f61,plain,(
% 2.64/0.75    m1_pre_topc(sK4,sK2)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f153,plain,(
% 2.64/0.75    ~spl9_11),
% 2.64/0.75    inference(avatar_split_clause,[],[f62,f150])).
% 2.64/0.75  fof(f62,plain,(
% 2.64/0.75    ~v2_struct_0(sK5)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f148,plain,(
% 2.64/0.75    spl9_10),
% 2.64/0.75    inference(avatar_split_clause,[],[f63,f145])).
% 2.64/0.75  fof(f63,plain,(
% 2.64/0.75    m1_pre_topc(sK5,sK2)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f143,plain,(
% 2.64/0.75    spl9_9),
% 2.64/0.75    inference(avatar_split_clause,[],[f64,f140])).
% 2.64/0.75  fof(f64,plain,(
% 2.64/0.75    v1_funct_1(sK6)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f138,plain,(
% 2.64/0.75    spl9_8),
% 2.64/0.75    inference(avatar_split_clause,[],[f65,f135])).
% 2.64/0.75  fof(f65,plain,(
% 2.64/0.75    v1_funct_2(sK6,u1_struct_0(sK5),u1_struct_0(sK3))),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f133,plain,(
% 2.64/0.75    spl9_7),
% 2.64/0.75    inference(avatar_split_clause,[],[f66,f130])).
% 2.64/0.75  fof(f66,plain,(
% 2.64/0.75    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK5),u1_struct_0(sK3))))),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f128,plain,(
% 2.64/0.75    spl9_6),
% 2.64/0.75    inference(avatar_split_clause,[],[f67,f125])).
% 2.64/0.75  fof(f67,plain,(
% 2.64/0.75    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = sK5),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f123,plain,(
% 2.64/0.75    spl9_5),
% 2.64/0.75    inference(avatar_split_clause,[],[f68,f120])).
% 2.64/0.75  fof(f68,plain,(
% 2.64/0.75    m1_subset_1(sK7,u1_struct_0(sK5))),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f118,plain,(
% 2.64/0.75    spl9_4),
% 2.64/0.75    inference(avatar_split_clause,[],[f69,f115])).
% 2.64/0.75  fof(f69,plain,(
% 2.64/0.75    m1_subset_1(sK8,u1_struct_0(sK4))),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f113,plain,(
% 2.64/0.75    spl9_3),
% 2.64/0.75    inference(avatar_split_clause,[],[f70,f110])).
% 2.64/0.75  fof(f70,plain,(
% 2.64/0.75    sK7 = sK8),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f108,plain,(
% 2.64/0.75    spl9_2),
% 2.64/0.75    inference(avatar_split_clause,[],[f71,f105])).
% 2.64/0.75  fof(f71,plain,(
% 2.64/0.75    r1_tmap_1(sK4,sK3,k3_tmap_1(sK2,sK3,sK5,sK4,sK6),sK8)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  fof(f103,plain,(
% 2.64/0.75    ~spl9_1),
% 2.64/0.75    inference(avatar_split_clause,[],[f72,f100])).
% 2.64/0.75  fof(f72,plain,(
% 2.64/0.75    ~r1_tmap_1(sK5,sK3,sK6,sK7)),
% 2.64/0.75    inference(cnf_transformation,[],[f47])).
% 2.64/0.75  % SZS output end Proof for theBenchmark
% 2.64/0.75  % (19781)------------------------------
% 2.64/0.75  % (19781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.64/0.75  % (19781)Termination reason: Refutation
% 2.64/0.75  
% 2.64/0.75  % (19781)Memory used [KB]: 14200
% 2.64/0.75  % (19781)Time elapsed: 0.336 s
% 2.64/0.75  % (19781)------------------------------
% 2.64/0.75  % (19781)------------------------------
% 2.64/0.75  % (19764)Success in time 0.396 s
%------------------------------------------------------------------------------
