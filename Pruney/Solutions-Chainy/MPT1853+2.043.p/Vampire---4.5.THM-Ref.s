%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:48 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  217 ( 385 expanded)
%              Number of leaves         :   50 ( 172 expanded)
%              Depth                    :    7
%              Number of atoms          :  819 (1364 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f76,f80,f87,f90,f94,f98,f102,f110,f114,f118,f126,f130,f134,f142,f146,f150,f154,f158,f165,f175,f185,f197,f206,f210,f226,f232,f237,f240,f244,f264,f276,f293,f298,f301,f312,f340,f347,f355,f378,f400])).

fof(f400,plain,
    ( ~ spl3_43
    | spl3_36
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f397,f208,f204,f78,f74,f70,f247,f291])).

fof(f291,plain,
    ( spl3_43
  <=> l1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f247,plain,
    ( spl3_36
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f70,plain,
    ( spl3_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f74,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f78,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f204,plain,
    ( spl3_30
  <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f208,plain,
    ( spl3_31
  <=> ! [X1,X0,X2] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f397,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) )
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f396,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f395,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl3_2
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f386,f75])).

fof(f75,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f74])).

fof(f386,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_struct_0(k1_tex_2(sK0,sK1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl3_30
    | ~ spl3_31 ),
    inference(superposition,[],[f209,f205])).

fof(f205,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f209,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f378,plain,
    ( spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_42 ),
    inference(avatar_contradiction_clause,[],[f377])).

fof(f377,plain,
    ( $false
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f376,f71])).

fof(f376,plain,
    ( v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_15
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f375,f79])).

fof(f375,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_2
    | ~ spl3_15
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f372,f75])).

fof(f372,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl3_15
    | ~ spl3_42 ),
    inference(resolution,[],[f289,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( ~ v2_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f289,plain,
    ( v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl3_42
  <=> v2_struct_0(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f355,plain,
    ( ~ spl3_3
    | ~ spl3_5
    | ~ spl3_36 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f351,f79])).

fof(f351,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl3_5
    | ~ spl3_36 ),
    inference(resolution,[],[f86,f248])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f247])).

fof(f86,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_5
  <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f347,plain,
    ( ~ spl3_2
    | ~ spl3_4
    | ~ spl3_23
    | spl3_45
    | ~ spl3_48 ),
    inference(avatar_contradiction_clause,[],[f346])).

fof(f346,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_23
    | spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f345,f83])).

fof(f83,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_4
  <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f345,plain,
    ( ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_23
    | spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f344,f75])).

fof(f344,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_23
    | spl3_45
    | ~ spl3_48 ),
    inference(subsumption_resolution,[],[f342,f311])).

fof(f311,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl3_45
  <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f342,plain,
    ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_23
    | ~ spl3_48 ),
    inference(resolution,[],[f339,f164])).

fof(f164,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl3_23
  <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f339,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),X3)
        | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3))
        | ~ l1_pre_topc(X3)
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),X3) )
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl3_48
  <=> ! [X3] :
        ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f340,plain,
    ( spl3_48
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f319,f204,f148,f338])).

fof(f148,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f319,plain,
    ( ! [X3] :
        ( v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3))
        | ~ m1_pre_topc(k1_tex_2(sK0,sK1),X3)
        | ~ l1_pre_topc(X3)
        | ~ v1_tex_2(k1_tex_2(sK0,sK1),X3) )
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(superposition,[],[f149,f205])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_tex_2(X1,X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f148])).

fof(f312,plain,
    ( ~ spl3_45
    | ~ spl3_10
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f306,f274,f108,f310])).

fof(f108,plain,
    ( spl3_10
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f274,plain,
    ( spl3_40
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f306,plain,
    ( ~ v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl3_10
    | ~ spl3_40 ),
    inference(resolution,[],[f275,f109])).

fof(f109,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
        | ~ v1_subset_1(X1,X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f275,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f301,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | ~ spl3_23
    | spl3_44 ),
    inference(avatar_contradiction_clause,[],[f299])).

fof(f299,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_23
    | spl3_44 ),
    inference(unit_resulting_resolution,[],[f75,f164,f297,f97])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f297,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl3_44
  <=> l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f298,plain,
    ( ~ spl3_44
    | ~ spl3_6
    | spl3_43 ),
    inference(avatar_split_clause,[],[f294,f291,f92,f296])).

fof(f92,plain,
    ( spl3_6
  <=> ! [X0] :
        ( ~ l1_pre_topc(X0)
        | l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f294,plain,
    ( ~ l1_pre_topc(k1_tex_2(sK0,sK1))
    | ~ spl3_6
    | spl3_43 ),
    inference(resolution,[],[f292,f93])).

fof(f93,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f292,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f291])).

fof(f293,plain,
    ( spl3_42
    | ~ spl3_43
    | ~ spl3_25
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f286,f262,f201,f173,f291,f288])).

fof(f173,plain,
    ( spl3_25
  <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f201,plain,
    ( spl3_29
  <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f262,plain,
    ( spl3_39
  <=> ! [X0] :
        ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f286,plain,
    ( ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_25
    | ~ spl3_29
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f285,f202])).

fof(f202,plain,
    ( v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f201])).

fof(f285,plain,
    ( ~ v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ l1_struct_0(k1_tex_2(sK0,sK1))
    | v2_struct_0(k1_tex_2(sK0,sK1))
    | ~ spl3_25
    | ~ spl3_39 ),
    inference(resolution,[],[f263,f174])).

fof(f174,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f173])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f262])).

fof(f276,plain,
    ( spl3_40
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f267,f204,f173,f274])).

fof(f267,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_25
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f174,f205])).

fof(f264,plain,
    ( spl3_39
    | ~ spl3_8
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f245,f242,f100,f262])).

fof(f100,plain,
    ( spl3_8
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f242,plain,
    ( spl3_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_8
    | ~ spl3_35 ),
    inference(resolution,[],[f243,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f243,plain,
    ( ! [X0] :
        ( v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f242])).

fof(f244,plain,
    ( spl3_35
    | spl3_32
    | ~ spl3_18
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f238,f224,f140,f221,f242])).

fof(f221,plain,
    ( spl3_32
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f140,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | ~ v1_zfmisc_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f224,plain,
    ( spl3_33
  <=> v1_zfmisc_1(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f238,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl3_18
    | ~ spl3_33 ),
    inference(resolution,[],[f225,f141])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ v1_zfmisc_1(X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_xboole_0(X1)
        | ~ v1_subset_1(X1,X0) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f225,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f224])).

fof(f240,plain,
    ( spl3_4
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f215,f201,f195,f163,f74,f82])).

fof(f195,plain,
    ( spl3_28
  <=> ! [X1,X0] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f215,plain,
    ( v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_23
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f214,f75])).

fof(f214,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_23
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f212,f164])).

fof(f212,plain,
    ( ~ m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_28
    | ~ spl3_29 ),
    inference(resolution,[],[f202,f196])).

fof(f196,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f195])).

fof(f237,plain,
    ( ~ spl3_2
    | ~ spl3_6
    | spl3_34 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_6
    | spl3_34 ),
    inference(subsumption_resolution,[],[f234,f75])).

fof(f234,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_6
    | spl3_34 ),
    inference(resolution,[],[f231,f93])).

fof(f231,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_34 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl3_34
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f232,plain,
    ( ~ spl3_34
    | spl3_1
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f228,f221,f100,f70,f230])).

fof(f228,plain,
    ( ~ l1_struct_0(sK0)
    | spl3_1
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f227,f71])).

fof(f227,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_8
    | ~ spl3_32 ),
    inference(resolution,[],[f222,f101])).

fof(f222,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f221])).

fof(f226,plain,
    ( spl3_32
    | spl3_33
    | ~ spl3_3
    | spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f219,f124,f85,f78,f224,f221])).

fof(f124,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | v1_zfmisc_1(X0)
        | ~ m1_subset_1(X1,X0)
        | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f219,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_3
    | spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f218,f79])).

fof(f218,plain,
    ( v1_zfmisc_1(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl3_5
    | ~ spl3_14 ),
    inference(resolution,[],[f89,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( v1_subset_1(k6_domain_1(X0,X1),X0)
        | v1_zfmisc_1(X0)
        | ~ m1_subset_1(X1,X0)
        | v1_xboole_0(X0) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f89,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f210,plain,
    ( spl3_31
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f191,f183,f132,f128,f208])).

fof(f132,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f183,plain,
    ( spl3_26
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
        | ~ v7_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f191,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f190,f129])).

fof(f190,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_struct_0(k1_tex_2(X0,X1))
        | ~ m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1)))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1)))
        | v2_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(resolution,[],[f184,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( v7_struct_0(k1_tex_2(X0,X1))
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ v7_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f183])).

fof(f206,plain,
    ( spl3_29
    | spl3_30
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f178,f173,f112,f204,f201])).

fof(f112,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f178,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))
    | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(resolution,[],[f174,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | X0 = X1
        | v1_subset_1(X1,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f197,plain,
    ( spl3_28
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f177,f156,f152,f195])).

fof(f152,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | u1_struct_0(X1) = sK2(X0,X1)
        | v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f156,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        | v1_tex_2(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) )
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) )
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(superposition,[],[f157,f153])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( u1_struct_0(X1) = sK2(X0,X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f152])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | v1_tex_2(X1,X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f156])).

fof(f185,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f54,f183])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).

fof(f175,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f167,f163,f116,f74,f173])).

fof(f116,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f167,plain,
    ( m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f166,f75])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(resolution,[],[f164,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0)
        | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f165,plain,
    ( spl3_23
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f161,f144,f78,f74,f70,f163])).

fof(f144,plain,
    ( spl3_19
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f161,plain,
    ( m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f160,f71])).

fof(f160,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(subsumption_resolution,[],[f159,f75])).

fof(f159,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_pre_topc(k1_tex_2(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_19 ),
    inference(resolution,[],[f145,f79])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0)
        | m1_pre_topc(k1_tex_2(X0,X1),X0) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f144])).

fof(f158,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f52,f156])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( v1_subset_1(X2,u1_struct_0(X0))
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v1_subset_1(X2,u1_struct_0(X0)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).

fof(f154,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f51,f152])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f150,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f68,f148])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f66,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_subset_1(X2,u1_struct_0(X0))
      | ~ v1_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f146,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f65,f144])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f142,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f56,f140])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v1_subset_1(X1,X0)
          | v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( ~ v1_xboole_0(X1)
           => ~ v1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

fof(f134,plain,(
    spl3_16 ),
    inference(avatar_split_clause,[],[f61,f132])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f130,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f60,f128])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f126,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).

fof(f118,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f48,f116])).

fof(f114,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f110,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f67,f108])).

fof(f67,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f53,f100])).

fof(f53,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f98,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f47,f96])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f94,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f46,f92])).

fof(f46,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f90,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f41,f85,f82])).

fof(f41,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | ~ v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v1_tex_2(k1_tex_2(X0,X1),X0)
            <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).

fof(f87,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f40,f85,f82])).

fof(f40,plain,
    ( v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    | v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f42,f78])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f44,f74])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f43,f70])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:33:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (31744)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (31752)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (31744)Refutation not found, incomplete strategy% (31744)------------------------------
% 0.21/0.49  % (31744)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (31744)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (31744)Memory used [KB]: 6140
% 0.21/0.49  % (31744)Time elapsed: 0.068 s
% 0.21/0.49  % (31744)------------------------------
% 0.21/0.49  % (31744)------------------------------
% 0.21/0.50  % (31736)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (31739)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (31743)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (31747)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (31748)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (31734)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (31738)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.52  % (31747)Refutation not found, incomplete strategy% (31747)------------------------------
% 0.21/0.52  % (31747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31747)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31747)Memory used [KB]: 1663
% 0.21/0.52  % (31747)Time elapsed: 0.089 s
% 0.21/0.52  % (31747)------------------------------
% 0.21/0.52  % (31747)------------------------------
% 0.21/0.52  % (31743)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f401,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f72,f76,f80,f87,f90,f94,f98,f102,f110,f114,f118,f126,f130,f134,f142,f146,f150,f154,f158,f165,f175,f185,f197,f206,f210,f226,f232,f237,f240,f244,f264,f276,f293,f298,f301,f312,f340,f347,f355,f378,f400])).
% 0.21/0.52  fof(f400,plain,(
% 0.21/0.52    ~spl3_43 | spl3_36 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_30 | ~spl3_31),
% 0.21/0.52    inference(avatar_split_clause,[],[f397,f208,f204,f78,f74,f70,f247,f291])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    spl3_43 <=> l1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    spl3_36 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    spl3_1 <=> v2_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl3_2 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    spl3_3 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.52  fof(f204,plain,(
% 0.21/0.52    spl3_30 <=> u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl3_31 <=> ! [X1,X0,X2] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.52  fof(f397,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0))) ) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_30 | ~spl3_31)),
% 0.21/0.52    inference(subsumption_resolution,[],[f396,f71])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    ~v2_struct_0(sK0) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f70])).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_3 | ~spl3_30 | ~spl3_31)),
% 0.21/0.52    inference(subsumption_resolution,[],[f395,f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f78])).
% 0.21/0.52  fof(f395,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl3_2 | ~spl3_30 | ~spl3_31)),
% 0.21/0.52    inference(subsumption_resolution,[],[f386,f75])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl3_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f74])).
% 0.21/0.52  fof(f386,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | (~spl3_30 | ~spl3_31)),
% 0.21/0.52    inference(superposition,[],[f209,f205])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f204])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~l1_struct_0(k1_tex_2(X0,X1)) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_31),
% 0.21/0.52    inference(avatar_component_clause,[],[f208])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_15 | ~spl3_42),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f377])).
% 0.21/0.52  fof(f377,plain,(
% 0.21/0.52    $false | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_15 | ~spl3_42)),
% 0.21/0.52    inference(subsumption_resolution,[],[f376,f71])).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    v2_struct_0(sK0) | (~spl3_2 | ~spl3_3 | ~spl3_15 | ~spl3_42)),
% 0.21/0.52    inference(subsumption_resolution,[],[f375,f79])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_2 | ~spl3_15 | ~spl3_42)),
% 0.21/0.52    inference(subsumption_resolution,[],[f372,f75])).
% 0.21/0.52  fof(f372,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl3_15 | ~spl3_42)),
% 0.21/0.52    inference(resolution,[],[f289,f129])).
% 0.21/0.52  fof(f129,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl3_15 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    v2_struct_0(k1_tex_2(sK0,sK1)) | ~spl3_42),
% 0.21/0.52    inference(avatar_component_clause,[],[f288])).
% 0.21/0.52  fof(f288,plain,(
% 0.21/0.52    spl3_42 <=> v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.52  fof(f355,plain,(
% 0.21/0.52    ~spl3_3 | ~spl3_5 | ~spl3_36),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f354])).
% 0.21/0.52  fof(f354,plain,(
% 0.21/0.52    $false | (~spl3_3 | ~spl3_5 | ~spl3_36)),
% 0.21/0.52    inference(subsumption_resolution,[],[f351,f79])).
% 0.21/0.52  fof(f351,plain,(
% 0.21/0.52    ~m1_subset_1(sK1,u1_struct_0(sK0)) | (~spl3_5 | ~spl3_36)),
% 0.21/0.52    inference(resolution,[],[f86,f248])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    ( ! [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl3_36),
% 0.21/0.52    inference(avatar_component_clause,[],[f247])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl3_5 <=> v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f347,plain,(
% 0.21/0.52    ~spl3_2 | ~spl3_4 | ~spl3_23 | spl3_45 | ~spl3_48),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f346])).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    $false | (~spl3_2 | ~spl3_4 | ~spl3_23 | spl3_45 | ~spl3_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f345,f83])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    spl3_4 <=> v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_2 | ~spl3_23 | spl3_45 | ~spl3_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f344,f75])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_23 | spl3_45 | ~spl3_48)),
% 0.21/0.52    inference(subsumption_resolution,[],[f342,f311])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | spl3_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f310])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    spl3_45 <=> v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.52  fof(f342,plain,(
% 0.21/0.52    v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_23 | ~spl3_48)),
% 0.21/0.52    inference(resolution,[],[f339,f164])).
% 0.21/0.52  fof(f164,plain,(
% 0.21/0.52    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~spl3_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl3_23 <=> m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.52  fof(f339,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_pre_topc(k1_tex_2(sK0,sK1),X3) | v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3)) | ~l1_pre_topc(X3) | ~v1_tex_2(k1_tex_2(sK0,sK1),X3)) ) | ~spl3_48),
% 0.21/0.52    inference(avatar_component_clause,[],[f338])).
% 0.21/0.52  fof(f338,plain,(
% 0.21/0.52    spl3_48 <=> ! [X3] : (v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X3) | ~l1_pre_topc(X3) | ~v1_tex_2(k1_tex_2(sK0,sK1),X3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.52  fof(f340,plain,(
% 0.21/0.52    spl3_48 | ~spl3_20 | ~spl3_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f319,f204,f148,f338])).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl3_20 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    ( ! [X3] : (v1_subset_1(u1_struct_0(sK0),u1_struct_0(X3)) | ~m1_pre_topc(k1_tex_2(sK0,sK1),X3) | ~l1_pre_topc(X3) | ~v1_tex_2(k1_tex_2(sK0,sK1),X3)) ) | (~spl3_20 | ~spl3_30)),
% 0.21/0.52    inference(superposition,[],[f149,f205])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v1_tex_2(X1,X0)) ) | ~spl3_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f148])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ~spl3_45 | ~spl3_10 | ~spl3_40),
% 0.21/0.52    inference(avatar_split_clause,[],[f306,f274,f108,f310])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    spl3_10 <=> ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl3_40 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl3_10 | ~spl3_40)),
% 0.21/0.52    inference(resolution,[],[f275,f109])).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) ) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f108])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_40),
% 0.21/0.52    inference(avatar_component_clause,[],[f274])).
% 0.21/0.52  fof(f301,plain,(
% 0.21/0.52    ~spl3_2 | ~spl3_7 | ~spl3_23 | spl3_44),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f299])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    $false | (~spl3_2 | ~spl3_7 | ~spl3_23 | spl3_44)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f75,f164,f297,f97])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) ) | ~spl3_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl3_7 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | spl3_44),
% 0.21/0.52    inference(avatar_component_clause,[],[f296])).
% 0.21/0.52  fof(f296,plain,(
% 0.21/0.52    spl3_44 <=> l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    ~spl3_44 | ~spl3_6 | spl3_43),
% 0.21/0.52    inference(avatar_split_clause,[],[f294,f291,f92,f296])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl3_6 <=> ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f294,plain,(
% 0.21/0.52    ~l1_pre_topc(k1_tex_2(sK0,sK1)) | (~spl3_6 | spl3_43)),
% 0.21/0.52    inference(resolution,[],[f292,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    ~l1_struct_0(k1_tex_2(sK0,sK1)) | spl3_43),
% 0.21/0.52    inference(avatar_component_clause,[],[f291])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    spl3_42 | ~spl3_43 | ~spl3_25 | ~spl3_29 | ~spl3_39),
% 0.21/0.52    inference(avatar_split_clause,[],[f286,f262,f201,f173,f291,f288])).
% 0.21/0.52  fof(f173,plain,(
% 0.21/0.52    spl3_25 <=> m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.52  fof(f201,plain,(
% 0.21/0.52    spl3_29 <=> v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.52  fof(f262,plain,(
% 0.21/0.52    spl3_39 <=> ! [X0] : (~v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl3_25 | ~spl3_29 | ~spl3_39)),
% 0.21/0.52    inference(subsumption_resolution,[],[f285,f202])).
% 0.21/0.52  fof(f202,plain,(
% 0.21/0.52    v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~spl3_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f201])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    ~v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | ~l1_struct_0(k1_tex_2(sK0,sK1)) | v2_struct_0(k1_tex_2(sK0,sK1)) | (~spl3_25 | ~spl3_39)),
% 0.21/0.52    inference(resolution,[],[f263,f174])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f173])).
% 0.21/0.52  fof(f263,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_39),
% 0.21/0.52    inference(avatar_component_clause,[],[f262])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    spl3_40 | ~spl3_25 | ~spl3_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f267,f204,f173,f274])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_25 | ~spl3_30)),
% 0.21/0.52    inference(backward_demodulation,[],[f174,f205])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    spl3_39 | ~spl3_8 | ~spl3_35),
% 0.21/0.52    inference(avatar_split_clause,[],[f245,f242,f100,f262])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl3_8 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl3_35 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.52  fof(f245,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_subset_1(u1_struct_0(X0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | (~spl3_8 | ~spl3_35)),
% 0.21/0.52    inference(resolution,[],[f243,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f100])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_35),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl3_35 | spl3_32 | ~spl3_18 | ~spl3_33),
% 0.21/0.52    inference(avatar_split_clause,[],[f238,f224,f140,f221,f242])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    spl3_32 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl3_18 <=> ! [X1,X0] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.52  fof(f224,plain,(
% 0.21/0.52    spl3_33 <=> v1_zfmisc_1(u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ( ! [X0] : (v1_xboole_0(u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl3_18 | ~spl3_33)),
% 0.21/0.52    inference(resolution,[],[f225,f141])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_zfmisc_1(X0) | v1_xboole_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) ) | ~spl3_18),
% 0.21/0.52    inference(avatar_component_clause,[],[f140])).
% 0.21/0.52  fof(f225,plain,(
% 0.21/0.52    v1_zfmisc_1(u1_struct_0(sK0)) | ~spl3_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f224])).
% 0.21/0.52  fof(f240,plain,(
% 0.21/0.52    spl3_4 | ~spl3_2 | ~spl3_23 | ~spl3_28 | ~spl3_29),
% 0.21/0.52    inference(avatar_split_clause,[],[f215,f201,f195,f163,f74,f82])).
% 0.21/0.52  fof(f195,plain,(
% 0.21/0.52    spl3_28 <=> ! [X1,X0] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.52  fof(f215,plain,(
% 0.21/0.52    v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_2 | ~spl3_23 | ~spl3_28 | ~spl3_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f214,f75])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_23 | ~spl3_28 | ~spl3_29)),
% 0.21/0.52    inference(subsumption_resolution,[],[f212,f164])).
% 0.21/0.52  fof(f212,plain,(
% 0.21/0.52    ~m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | v1_tex_2(k1_tex_2(sK0,sK1),sK0) | (~spl3_28 | ~spl3_29)),
% 0.21/0.52    inference(resolution,[],[f202,f196])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) ) | ~spl3_28),
% 0.21/0.52    inference(avatar_component_clause,[],[f195])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    ~spl3_2 | ~spl3_6 | spl3_34),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    $false | (~spl3_2 | ~spl3_6 | spl3_34)),
% 0.21/0.52    inference(subsumption_resolution,[],[f234,f75])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | (~spl3_6 | spl3_34)),
% 0.21/0.52    inference(resolution,[],[f231,f93])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | spl3_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f230])).
% 0.21/0.52  fof(f230,plain,(
% 0.21/0.52    spl3_34 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~spl3_34 | spl3_1 | ~spl3_8 | ~spl3_32),
% 0.21/0.52    inference(avatar_split_clause,[],[f228,f221,f100,f70,f230])).
% 0.21/0.52  fof(f228,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | (spl3_1 | ~spl3_8 | ~spl3_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f227,f71])).
% 0.21/0.52  fof(f227,plain,(
% 0.21/0.52    ~l1_struct_0(sK0) | v2_struct_0(sK0) | (~spl3_8 | ~spl3_32)),
% 0.21/0.52    inference(resolution,[],[f222,f101])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f221])).
% 0.21/0.52  fof(f226,plain,(
% 0.21/0.52    spl3_32 | spl3_33 | ~spl3_3 | spl3_5 | ~spl3_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f219,f124,f85,f78,f224,f221])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl3_14 <=> ! [X1,X0] : (v1_xboole_0(X0) | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    v1_zfmisc_1(u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (~spl3_3 | spl3_5 | ~spl3_14)),
% 0.21/0.52    inference(subsumption_resolution,[],[f218,f79])).
% 0.21/0.52  fof(f218,plain,(
% 0.21/0.52    v1_zfmisc_1(u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | (spl3_5 | ~spl3_14)),
% 0.21/0.52    inference(resolution,[],[f89,f125])).
% 0.21/0.52  fof(f125,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) ) | ~spl3_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f124])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f85])).
% 0.21/0.52  fof(f210,plain,(
% 0.21/0.52    spl3_31 | ~spl3_15 | ~spl3_16 | ~spl3_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f191,f183,f132,f128,f208])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl3_16 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f183,plain,(
% 0.21/0.52    spl3_26 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.52  fof(f191,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | (~spl3_15 | ~spl3_16 | ~spl3_26)),
% 0.21/0.52    inference(subsumption_resolution,[],[f190,f129])).
% 0.21/0.52  fof(f190,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_struct_0(k1_tex_2(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(k1_tex_2(X0,X1))) | ~v1_subset_1(k6_domain_1(u1_struct_0(k1_tex_2(X0,X1)),X2),u1_struct_0(k1_tex_2(X0,X1))) | v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | (~spl3_16 | ~spl3_26)),
% 0.21/0.52    inference(resolution,[],[f184,f133])).
% 0.21/0.52  fof(f133,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f132])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | v2_struct_0(X0)) ) | ~spl3_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f183])).
% 0.21/0.52  fof(f206,plain,(
% 0.21/0.52    spl3_29 | spl3_30 | ~spl3_11 | ~spl3_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f178,f173,f112,f204,f201])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl3_11 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f178,plain,(
% 0.21/0.52    u1_struct_0(sK0) = u1_struct_0(k1_tex_2(sK0,sK1)) | v1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),u1_struct_0(sK0)) | (~spl3_11 | ~spl3_25)),
% 0.21/0.52    inference(resolution,[],[f174,f113])).
% 0.21/0.52  fof(f113,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) ) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f112])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    spl3_28 | ~spl3_21 | ~spl3_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f177,f156,f152,f195])).
% 0.21/0.52  fof(f152,plain,(
% 0.21/0.52    spl3_21 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    spl3_22 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) ) | (~spl3_21 | ~spl3_22)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f176])).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) ) | (~spl3_21 | ~spl3_22)),
% 0.21/0.52    inference(superposition,[],[f157,f153])).
% 0.21/0.52  fof(f153,plain,(
% 0.21/0.52    ( ! [X0,X1] : (u1_struct_0(X1) = sK2(X0,X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) ) | ~spl3_21),
% 0.21/0.52    inference(avatar_component_clause,[],[f152])).
% 0.21/0.52  fof(f157,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tex_2(X1,X0)) ) | ~spl3_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f156])).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl3_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f54,f183])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_tex_2)).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    spl3_25 | ~spl3_2 | ~spl3_12 | ~spl3_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f167,f163,f116,f74,f173])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl3_12 <=> ! [X1,X0] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_12 | ~spl3_23)),
% 0.21/0.52    inference(subsumption_resolution,[],[f166,f75])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(k1_tex_2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_12 | ~spl3_23)),
% 0.21/0.52    inference(resolution,[],[f164,f117])).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) ) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f116])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    spl3_23 | spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f161,f144,f78,f74,f70,f163])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl3_19 <=> ! [X1,X0] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (spl3_1 | ~spl3_2 | ~spl3_3 | ~spl3_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f160,f71])).
% 0.21/0.52  fof(f160,plain,(
% 0.21/0.52    v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl3_2 | ~spl3_3 | ~spl3_19)),
% 0.21/0.52    inference(subsumption_resolution,[],[f159,f75])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_pre_topc(k1_tex_2(sK0,sK1),sK0) | (~spl3_3 | ~spl3_19)),
% 0.21/0.52    inference(resolution,[],[f145,f79])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_pre_topc(k1_tex_2(X0,X1),X0)) ) | ~spl3_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl3_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f52,f156])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v1_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : (v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v1_tex_2(X1,X0) <=> ! [X2] : ((v1_subset_1(X2,u1_struct_0(X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v1_subset_1(X2,u1_struct_0(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tex_2)).
% 0.21/0.52  fof(f154,plain,(
% 0.21/0.52    spl3_21),
% 0.21/0.52    inference(avatar_split_clause,[],[f51,f152])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl3_20),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f148])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.52    inference(subsumption_resolution,[],[f66,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v1_subset_1(u1_struct_0(X1),u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_subset_1(X2,u1_struct_0(X0)) | ~v1_tex_2(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    spl3_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f144])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    spl3_18),
% 0.21/0.52    inference(avatar_split_clause,[],[f56,f140])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (~v1_subset_1(X1,X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((~v1_subset_1(X1,X0) | v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (~v1_xboole_0(X1) => ~v1_subset_1(X1,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl3_16),
% 0.21/0.52    inference(avatar_split_clause,[],[f61,f132])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f60,f128])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    spl3_14),
% 0.21/0.52    inference(avatar_split_clause,[],[f55,f124])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tex_2)).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f48,f116])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f58,f112])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f67,f108])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f35])).
% 0.21/0.52  fof(f102,plain,(
% 0.21/0.52    spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f53,f100])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f96])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f92])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    ~spl3_4 | ~spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f85,f82])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | ~v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <~> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tex_2)).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl3_4 | spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f85,f82])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) | v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f78])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f74])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f70])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~v2_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (31743)------------------------------
% 0.21/0.52  % (31743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31743)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (31743)Memory used [KB]: 10746
% 0.21/0.52  % (31743)Time elapsed: 0.094 s
% 0.21/0.52  % (31743)------------------------------
% 0.21/0.52  % (31743)------------------------------
% 0.21/0.52  % (31737)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (31737)Refutation not found, incomplete strategy% (31737)------------------------------
% 0.21/0.52  % (31737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (31737)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (31737)Memory used [KB]: 10618
% 0.21/0.52  % (31737)Time elapsed: 0.113 s
% 0.21/0.52  % (31737)------------------------------
% 0.21/0.52  % (31737)------------------------------
% 0.21/0.53  % (31742)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.53  % (31740)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.53  % (31750)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (31749)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.54  % (31733)Success in time 0.175 s
%------------------------------------------------------------------------------
