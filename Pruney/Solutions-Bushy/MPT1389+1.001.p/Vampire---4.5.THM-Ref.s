%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1389+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:51 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 411 expanded)
%              Number of leaves         :   54 ( 188 expanded)
%              Depth                    :    7
%              Number of atoms          :  982 (1869 expanded)
%              Number of equality atoms :   43 ( 102 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f481,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f85,f89,f97,f101,f105,f109,f113,f117,f121,f125,f129,f137,f141,f145,f153,f157,f162,f167,f171,f176,f189,f194,f200,f205,f209,f219,f238,f247,f251,f269,f288,f326,f329,f332,f341,f346,f395,f429,f443,f451,f459,f470,f478])).

fof(f478,plain,
    ( spl6_9
    | ~ spl6_39
    | ~ spl6_73 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl6_9
    | ~ spl6_39
    | ~ spl6_73 ),
    inference(subsumption_resolution,[],[f472,f108])).

fof(f108,plain,
    ( ~ r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2))
    | spl6_9 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl6_9
  <=> r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f472,plain,
    ( r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2))
    | ~ spl6_39
    | ~ spl6_73 ),
    inference(resolution,[],[f450,f246])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
        | r1_tarski(X0,k1_connsp_1(sK0,sK2)) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl6_39
  <=> ! [X0] :
        ( r1_tarski(X0,k1_connsp_1(sK0,sK2))
        | ~ r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f450,plain,
    ( r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f449])).

fof(f449,plain,
    ( spl6_73
  <=> r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f470,plain,
    ( ~ spl6_69
    | ~ spl6_6
    | ~ spl6_68
    | ~ spl6_74 ),
    inference(avatar_split_clause,[],[f465,f457,f424,f95,f427])).

fof(f427,plain,
    ( spl6_69
  <=> m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_69])])).

fof(f95,plain,
    ( spl6_6
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f424,plain,
    ( spl6_68
  <=> v2_connsp_1(k1_connsp_1(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f457,plain,
    ( spl6_74
  <=> ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f465,plain,
    ( ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_6
    | ~ spl6_68
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f464,f425])).

fof(f425,plain,
    ( v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f424])).

fof(f464,plain,
    ( ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ spl6_6
    | ~ spl6_74 ),
    inference(resolution,[],[f458,f96])).

fof(f96,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f458,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),X0) )
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f457])).

fof(f459,plain,
    ( spl6_74
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_72 ),
    inference(avatar_split_clause,[],[f455,f446,f151,f87,f83,f457])).

fof(f83,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f87,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f151,plain,
    ( spl6_20
  <=> ! [X1,X3,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_connsp_1(X3,X1)
        | v2_connsp_1(X3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f446,plain,
    ( spl6_72
  <=> v2_connsp_1(k1_connsp_1(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_72])])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),X0) )
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_20
    | spl6_72 ),
    inference(subsumption_resolution,[],[f454,f84])).

fof(f84,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f454,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_4
    | ~ spl6_20
    | spl6_72 ),
    inference(subsumption_resolution,[],[f452,f88])).

fof(f88,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f87])).

fof(f452,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),X0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl6_20
    | spl6_72 ),
    inference(resolution,[],[f447,f152])).

fof(f152,plain,
    ( ! [X0,X3,X1] :
        ( v2_connsp_1(X3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_connsp_1(X3,X1)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f447,plain,
    ( ~ v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | spl6_72 ),
    inference(avatar_component_clause,[],[f446])).

fof(f451,plain,
    ( ~ spl6_69
    | ~ spl6_72
    | spl6_73
    | ~ spl6_52
    | ~ spl6_50
    | spl6_1
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f398,f393,f103,f75,f318,f324,f449,f446,f427])).

fof(f324,plain,
    ( spl6_52
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f318,plain,
    ( spl6_50
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f75,plain,
    ( spl6_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f103,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f393,plain,
    ( spl6_62
  <=> ! [X0] :
        ( r2_hidden(k1_connsp_1(X0,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_connsp_1(k1_connsp_1(X0,sK2),sK0)
        | ~ m1_subset_1(k1_connsp_1(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f398,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_1
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f397,f76])).

fof(f76,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f397,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | v2_struct_0(sK1)
    | ~ v2_connsp_1(k1_connsp_1(sK1,sK2),sK0)
    | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_8
    | ~ spl6_62 ),
    inference(resolution,[],[f394,f104])).

fof(f104,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f103])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(k1_connsp_1(X0,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
        | v2_struct_0(X0)
        | ~ v2_connsp_1(k1_connsp_1(X0,sK2),sK0)
        | ~ m1_subset_1(k1_connsp_1(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f393])).

fof(f443,plain,
    ( ~ spl6_52
    | ~ spl6_8
    | ~ spl6_14
    | spl6_69 ),
    inference(avatar_split_clause,[],[f436,f427,f127,f103,f324])).

fof(f127,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f436,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl6_8
    | ~ spl6_14
    | spl6_69 ),
    inference(subsumption_resolution,[],[f434,f104])).

fof(f434,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_14
    | spl6_69 ),
    inference(resolution,[],[f428,f128])).

fof(f128,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f127])).

fof(f428,plain,
    ( ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | spl6_69 ),
    inference(avatar_component_clause,[],[f427])).

fof(f429,plain,
    ( ~ spl6_52
    | spl6_68
    | ~ spl6_69
    | ~ spl6_8
    | ~ spl6_29
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f350,f339,f192,f103,f427,f424,f324])).

fof(f192,plain,
    ( spl6_29
  <=> ! [X1,X0,X4] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_connsp_1(X4,X0)
        | ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f339,plain,
    ( spl6_54
  <=> r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK1,sK2,k1_connsp_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f350,plain,
    ( ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_8
    | ~ spl6_29
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f347,f104])).

fof(f347,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ m1_subset_1(k1_connsp_1(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v2_connsp_1(k1_connsp_1(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_29
    | ~ spl6_54 ),
    inference(resolution,[],[f340,f193])).

fof(f193,plain,
    ( ! [X4,X0,X1] :
        ( ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_connsp_1(X4,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f192])).

fof(f340,plain,
    ( r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK1,sK2,k1_connsp_1(sK1,sK2)))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f339])).

fof(f395,plain,
    ( spl6_62
    | ~ spl6_7
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f352,f344,f99,f393])).

fof(f99,plain,
    ( spl6_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f344,plain,
    ( spl6_55
  <=> ! [X1,X0] :
        ( ~ v2_connsp_1(k1_connsp_1(X0,X1),sK0)
        | r2_hidden(k1_connsp_1(X0,X1),sK4(sK0,X1,k1_connsp_1(sK0,X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f352,plain,
    ( ! [X0] :
        ( r2_hidden(k1_connsp_1(X0,sK2),sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_connsp_1(k1_connsp_1(X0,sK2),sK0)
        | ~ m1_subset_1(k1_connsp_1(X0,sK2),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_7
    | ~ spl6_55 ),
    inference(resolution,[],[f345,f100])).

fof(f100,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f345,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(k1_connsp_1(X0,X1),sK4(sK0,X1,k1_connsp_1(sK0,X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ v2_connsp_1(k1_connsp_1(X0,X1),sK0)
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f344])).

fof(f346,plain,
    ( spl6_55
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f294,f286,f95,f87,f344])).

fof(f286,plain,
    ( spl6_46
  <=> ! [X3,X5,X2,X4] :
        ( ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v2_connsp_1(k1_connsp_1(X4,X2),X3)
        | ~ l1_pre_topc(X3)
        | r2_hidden(k1_connsp_1(X4,X2),sK4(X3,X2,k1_connsp_1(X3,X2)))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X2,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_subset_1(k1_connsp_1(X4,X2),k1_zfmisc_1(u1_struct_0(X5))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( ~ v2_connsp_1(k1_connsp_1(X0,X1),sK0)
        | r2_hidden(k1_connsp_1(X0,X1),sK4(sK0,X1,k1_connsp_1(sK0,X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(subsumption_resolution,[],[f293,f88])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ v2_connsp_1(k1_connsp_1(X0,X1),sK0)
        | ~ l1_pre_topc(sK0)
        | r2_hidden(k1_connsp_1(X0,X1),sK4(sK0,X1,k1_connsp_1(sK0,X1)))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(sK1))) )
    | ~ spl6_6
    | ~ spl6_46 ),
    inference(resolution,[],[f287,f96])).

fof(f287,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ m1_pre_topc(X5,X3)
        | ~ v2_connsp_1(k1_connsp_1(X4,X2),X3)
        | ~ l1_pre_topc(X3)
        | r2_hidden(k1_connsp_1(X4,X2),sK4(X3,X2,k1_connsp_1(X3,X2)))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X2,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ m1_subset_1(k1_connsp_1(X4,X2),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f286])).

fof(f341,plain,
    ( spl6_54
    | ~ spl6_8
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f333,f321,f103,f339])).

fof(f321,plain,
    ( spl6_51
  <=> ! [X0] :
        ( r2_hidden(k1_connsp_1(sK1,X0),sK4(sK1,X0,k1_connsp_1(sK1,X0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f333,plain,
    ( r2_hidden(k1_connsp_1(sK1,sK2),sK4(sK1,sK2,k1_connsp_1(sK1,sK2)))
    | ~ spl6_8
    | ~ spl6_51 ),
    inference(resolution,[],[f322,f104])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r2_hidden(k1_connsp_1(sK1,X0),sK4(sK1,X0,k1_connsp_1(sK1,X0))) )
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f321])).

fof(f332,plain,
    ( ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | spl6_52 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_10
    | spl6_52 ),
    inference(unit_resulting_resolution,[],[f88,f96,f325,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( l1_pre_topc(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | l1_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f325,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_52 ),
    inference(avatar_component_clause,[],[f324])).

fof(f329,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12
    | spl6_50 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_12
    | spl6_50 ),
    inference(unit_resulting_resolution,[],[f84,f88,f96,f319,f120])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( v2_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl6_12
  <=> ! [X1,X0] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | v2_pre_topc(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f319,plain,
    ( ~ v2_pre_topc(sK1)
    | spl6_50 ),
    inference(avatar_component_clause,[],[f318])).

fof(f326,plain,
    ( ~ spl6_50
    | spl6_51
    | ~ spl6_52
    | spl6_1
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f270,f267,f75,f324,f321,f318])).

fof(f267,plain,
    ( spl6_43
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X1,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f270,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK1)
        | r2_hidden(k1_connsp_1(sK1,X0),sK4(sK1,X0,k1_connsp_1(sK1,X0)))
        | ~ v2_pre_topc(sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK1)) )
    | spl6_1
    | ~ spl6_43 ),
    inference(resolution,[],[f268,f76])).

fof(f268,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X1,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1)) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f267])).

fof(f288,plain,
    ( spl6_46
    | ~ spl6_16
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f254,f249,f135,f286])).

fof(f135,plain,
    ( spl6_16
  <=> ! [X1,X0,X2] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f249,plain,
    ( spl6_40
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(k1_connsp_1(X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_connsp_1(k1_connsp_1(X2,X0),X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X2,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X0,u1_struct_0(X2))
        | v2_struct_0(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f254,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v2_connsp_1(k1_connsp_1(X4,X2),X3)
        | ~ l1_pre_topc(X3)
        | r2_hidden(k1_connsp_1(X4,X2),sK4(X3,X2,k1_connsp_1(X3,X2)))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X2,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_subset_1(k1_connsp_1(X4,X2),k1_zfmisc_1(u1_struct_0(X5))) )
    | ~ spl6_16
    | ~ spl6_40 ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,
    ( ! [X4,X2,X5,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(X3))
        | ~ v2_connsp_1(k1_connsp_1(X4,X2),X3)
        | ~ l1_pre_topc(X3)
        | r2_hidden(k1_connsp_1(X4,X2),sK4(X3,X2,k1_connsp_1(X3,X2)))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X2,u1_struct_0(X4))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_subset_1(k1_connsp_1(X4,X2),k1_zfmisc_1(u1_struct_0(X5)))
        | ~ l1_pre_topc(X3) )
    | ~ spl6_16
    | ~ spl6_40 ),
    inference(resolution,[],[f250,f136])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f135])).

fof(f250,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_connsp_1(X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v2_connsp_1(k1_connsp_1(X2,X0),X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X2,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X0,u1_struct_0(X2))
        | v2_struct_0(X2) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f249])).

fof(f269,plain,
    ( spl6_43
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f256,f249,f143,f127,f267])).

fof(f143,plain,
    ( spl6_18
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_connsp_1(k1_connsp_1(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f256,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X1,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f255,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f255,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v2_connsp_1(k1_connsp_1(X1,X0),X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X1,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_14
    | ~ spl6_40 ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ v2_connsp_1(k1_connsp_1(X1,X0),X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X1,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1) )
    | ~ spl6_14
    | ~ spl6_40 ),
    inference(resolution,[],[f250,f128])).

fof(f251,plain,
    ( spl6_40
    | ~ spl6_17
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f210,f203,f139,f249])).

fof(f139,plain,
    ( spl6_17
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | r2_hidden(X1,k1_connsp_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f203,plain,
    ( spl6_31
  <=> ! [X1,X0,X4] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(X4,X0)
        | ~ r2_hidden(X1,X4)
        | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f210,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_subset_1(k1_connsp_1(X2,X0),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ v2_connsp_1(k1_connsp_1(X2,X0),X1)
        | ~ l1_pre_topc(X1)
        | r2_hidden(k1_connsp_1(X2,X0),sK4(X1,X0,k1_connsp_1(X1,X0)))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X0,u1_struct_0(X2))
        | v2_struct_0(X2) )
    | ~ spl6_17
    | ~ spl6_31 ),
    inference(resolution,[],[f204,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X1,k1_connsp_1(X0,X1))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | v2_struct_0(X0) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f139])).

fof(f204,plain,
    ( ! [X4,X0,X1] :
        ( ~ r2_hidden(X1,X4)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(X4,X0)
        | ~ l1_pre_topc(X0)
        | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f203])).

fof(f247,plain,
    ( spl6_39
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f239,f236,f115,f245])).

fof(f115,plain,
    ( spl6_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | r1_tarski(X0,k3_tarski(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f236,plain,
    ( spl6_37
  <=> k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f239,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_connsp_1(sK0,sK2))
        | ~ r2_hidden(X0,sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) )
    | ~ spl6_11
    | ~ spl6_37 ),
    inference(superposition,[],[f116,f237])).

fof(f237,plain,
    ( k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f236])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,k3_tarski(X1))
        | ~ r2_hidden(X0,X1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f238,plain,
    ( spl6_37
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f227,f217,f174,f99,f87,f236])).

fof(f174,plain,
    ( spl6_25
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f217,plain,
    ( spl6_34
  <=> k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f227,plain,
    ( k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f226,f88])).

fof(f226,plain,
    ( k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_7
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f224,f100])).

fof(f224,plain,
    ( k1_connsp_1(sK0,sK2) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_25
    | ~ spl6_34 ),
    inference(superposition,[],[f218,f175])).

fof(f175,plain,
    ( ! [X0,X1] :
        ( k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1)))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f174])).

fof(f218,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f217])).

fof(f219,plain,
    ( spl6_34
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f211,f207,f99,f217])).

fof(f207,plain,
    ( spl6_32
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_1(sK0,X0))) = k3_tarski(sK4(sK0,X0,k1_connsp_1(sK0,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f211,plain,
    ( k5_setfam_1(u1_struct_0(sK0),sK4(sK0,sK2,k1_connsp_1(sK0,sK2))) = k3_tarski(sK4(sK0,sK2,k1_connsp_1(sK0,sK2)))
    | ~ spl6_7
    | ~ spl6_32 ),
    inference(resolution,[],[f208,f100])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_1(sK0,X0))) = k3_tarski(sK4(sK0,X0,k1_connsp_1(sK0,X0))) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( spl6_32
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f195,f165,f87,f207])).

fof(f165,plain,
    ( spl6_23
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | k5_setfam_1(u1_struct_0(X1),sK4(X1,X0,k1_connsp_1(X1,X0))) = k3_tarski(sK4(X1,X0,k1_connsp_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_setfam_1(u1_struct_0(sK0),sK4(sK0,X0,k1_connsp_1(sK0,X0))) = k3_tarski(sK4(sK0,X0,k1_connsp_1(sK0,X0))) )
    | ~ spl6_4
    | ~ spl6_23 ),
    inference(resolution,[],[f166,f88])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | k5_setfam_1(u1_struct_0(X1),sK4(X1,X0,k1_connsp_1(X1,X0))) = k3_tarski(sK4(X1,X0,k1_connsp_1(X1,X0))) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f165])).

fof(f205,plain,
    ( spl6_31
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f201,f198,f127,f203])).

fof(f198,plain,
    ( spl6_30
  <=> ! [X1,X0,X4] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(X4,X0)
        | ~ r2_hidden(X1,X4)
        | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f201,plain,
    ( ! [X4,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(X4,X0)
        | ~ r2_hidden(X1,X4)
        | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_14
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f199,f128])).

fof(f199,plain,
    ( ! [X4,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v2_connsp_1(X4,X0)
        | ~ r2_hidden(X1,X4)
        | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f62,f198])).

fof(f62,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_connsp_1(X4,X0)
      | ~ r2_hidden(X1,X4)
      | r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_connsp_1(X4,X0)
      | ~ r2_hidden(X1,X4)
      | r2_hidden(X4,sK4(X0,X1,X2))
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) )
                        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( k1_connsp_1(X0,X1) = X2
              <=> ? [X3] :
                    ( k5_setfam_1(u1_struct_0(X0),X3) = X2
                    & ! [X4] :
                        ( m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X4,X3)
                        <=> ( r2_hidden(X1,X4)
                            & v2_connsp_1(X4,X0) ) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_connsp_1)).

fof(f194,plain,
    ( spl6_29
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f190,f187,f127,f192])).

fof(f187,plain,
    ( spl6_28
  <=> ! [X1,X0,X4] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_connsp_1(X4,X0)
        | ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f190,plain,
    ( ! [X4,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_connsp_1(X4,X0)
        | ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_14
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f188,f128])).

fof(f188,plain,
    ( ! [X4,X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_connsp_1(X4,X0)
        | ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f187])).

fof(f189,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f64,f187])).

fof(f64,plain,(
    ! [X4,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_connsp_1(X4,X0)
      | ~ r2_hidden(X4,sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_connsp_1(X4,X0)
      | ~ r2_hidden(X4,sK4(X0,X1,X2))
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f176,plain,
    ( spl6_25
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f172,f169,f127,f174])).

fof(f169,plain,
    ( spl6_24
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_14
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f170,f128])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f169])).

fof(f171,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f59,f169])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | k1_connsp_1(X0,X1) = k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,k1_connsp_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_setfam_1(u1_struct_0(X0),sK4(X0,X1,X2)) = X2
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f167,plain,
    ( spl6_23
    | ~ spl6_13
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f163,f160,f123,f165])).

fof(f123,plain,
    ( spl6_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f160,plain,
    ( spl6_22
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f163,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ l1_pre_topc(X1)
        | k5_setfam_1(u1_struct_0(X1),sK4(X1,X0,k1_connsp_1(X1,X0))) = k3_tarski(sK4(X1,X0,k1_connsp_1(X1,X0))) )
    | ~ spl6_13
    | ~ spl6_22 ),
    inference(resolution,[],[f161,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
        | k5_setfam_1(X0,X1) = k3_tarski(X1) )
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f160])).

fof(f162,plain,
    ( spl6_22
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f158,f155,f127,f160])).

fof(f155,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl6_14
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f156,f128])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,u1_struct_0(X0))
        | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
        | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,(
    spl6_21 ),
    inference(avatar_split_clause,[],[f60,f155])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,k1_connsp_1(X0,X1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | k1_connsp_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f153,plain,(
    spl6_20 ),
    inference(avatar_split_clause,[],[f73,f151])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X3,X0) ) ),
    inference(subsumption_resolution,[],[f69,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X3,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | ~ v2_connsp_1(X3,X1)
      | v2_connsp_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v2_connsp_1(X2,X0)
                  <=> v2_connsp_1(X3,X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_connsp_1(X2,X0)
                    <=> v2_connsp_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_connsp_1)).

fof(f145,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f57,f143])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_connsp_1(k1_connsp_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_connsp_1(k1_connsp_1(X0,X1),X0)
        & ~ v1_xboole_0(k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_connsp_1)).

fof(f141,plain,(
    spl6_17 ),
    inference(avatar_split_clause,[],[f50,f139])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(X1,k1_connsp_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,k1_connsp_1(X0,X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_hidden(X1,k1_connsp_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_connsp_1)).

fof(f137,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f40,f135])).

fof(f129,plain,(
    spl6_14 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_connsp_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_connsp_1)).

fof(f125,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f55,f123])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,X1) = k3_tarski(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k5_setfam_1(X0,X1) = k3_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f121,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f51,f119])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f117,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f54,f115])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_zfmisc_1)).

fof(f113,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f109,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f70,f107])).

fof(f70,plain,(
    ~ r1_tarski(k1_connsp_1(sK1,sK2),k1_connsp_1(sK0,sK2)) ),
    inference(backward_demodulation,[],[f32,f31])).

fof(f31,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2))
                  & X2 = X3
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ( X2 = X3
                     => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ( X2 = X3
                   => r1_tarski(k1_connsp_1(X1,X3),k1_connsp_1(X0,X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_connsp_2)).

fof(f32,plain,(
    ~ r1_tarski(k1_connsp_1(sK1,sK3),k1_connsp_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f71,f103])).

fof(f71,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(forward_demodulation,[],[f30,f31])).

fof(f30,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f101,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f33,f99])).

fof(f33,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f35,f95])).

fof(f35,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f85,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f77,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f75])).

fof(f34,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
