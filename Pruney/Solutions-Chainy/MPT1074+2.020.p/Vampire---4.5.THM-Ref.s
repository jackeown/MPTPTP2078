%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 296 expanded)
%              Number of leaves         :   45 ( 132 expanded)
%              Depth                    :    8
%              Number of atoms          :  605 (1033 expanded)
%              Number of equality atoms :   74 ( 105 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f103,f107,f111,f115,f119,f123,f127,f131,f135,f153,f162,f176,f209,f217,f263,f276,f279,f316,f320,f327,f332,f336,f371,f389,f406,f414,f456,f466,f484,f500,f517,f705,f712])).

fof(f712,plain,
    ( ~ spl8_47
    | spl8_76
    | ~ spl8_108 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl8_47
    | spl8_76
    | ~ spl8_108 ),
    inference(subsumption_resolution,[],[f707,f315])).

fof(f315,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl8_47
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f707,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl8_76
    | ~ spl8_108 ),
    inference(resolution,[],[f704,f516])).

fof(f516,plain,
    ( ~ r2_hidden(sK7(sK1,sK0,sK3),sK1)
    | spl8_76 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl8_76
  <=> r2_hidden(sK7(sK1,sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).

fof(f704,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_108 ),
    inference(avatar_component_clause,[],[f703])).

fof(f703,plain,
    ( spl8_108
  <=> ! [X0] :
        ( r2_hidden(sK7(sK1,X0,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).

fof(f705,plain,
    ( ~ spl8_40
    | spl8_108
    | ~ spl8_1
    | ~ spl8_49
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f424,f404,f325,f93,f703,f274])).

fof(f274,plain,
    ( spl8_40
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f93,plain,
    ( spl8_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f325,plain,
    ( spl8_49
  <=> ! [X1,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f404,plain,
    ( spl8_63
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).

fof(f424,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK1,X0,sK3),sK1)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_1
    | ~ spl8_49
    | ~ spl8_63 ),
    inference(subsumption_resolution,[],[f420,f94])).

fof(f94,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f420,plain,
    ( ! [X0] :
        ( r2_hidden(sK7(sK1,X0,sK3),sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_49
    | ~ spl8_63 ),
    inference(superposition,[],[f326,f405])).

fof(f405,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl8_63 ),
    inference(avatar_component_clause,[],[f404])).

fof(f326,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) )
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f325])).

fof(f517,plain,
    ( ~ spl8_76
    | ~ spl8_11
    | spl8_74 ),
    inference(avatar_split_clause,[],[f505,f498,f133,f515])).

fof(f133,plain,
    ( spl8_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f498,plain,
    ( spl8_74
  <=> m1_subset_1(sK7(sK1,sK0,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).

fof(f505,plain,
    ( ~ r2_hidden(sK7(sK1,sK0,sK3),sK1)
    | ~ spl8_11
    | spl8_74 ),
    inference(resolution,[],[f499,f134])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f133])).

fof(f499,plain,
    ( ~ m1_subset_1(sK7(sK1,sK0,sK3),sK1)
    | spl8_74 ),
    inference(avatar_component_clause,[],[f498])).

fof(f500,plain,
    ( ~ spl8_74
    | ~ spl8_47
    | ~ spl8_67
    | ~ spl8_71 ),
    inference(avatar_split_clause,[],[f490,f482,f454,f314,f498])).

fof(f454,plain,
    ( spl8_67
  <=> ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).

fof(f482,plain,
    ( spl8_71
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).

fof(f490,plain,
    ( ~ m1_subset_1(sK7(sK1,sK0,sK3),sK1)
    | ~ spl8_47
    | ~ spl8_67
    | ~ spl8_71 ),
    inference(subsumption_resolution,[],[f489,f315])).

fof(f489,plain,
    ( ~ m1_subset_1(sK7(sK1,sK0,sK3),sK1)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl8_67
    | ~ spl8_71 ),
    inference(resolution,[],[f483,f455])).

fof(f455,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) )
    | ~ spl8_67 ),
    inference(avatar_component_clause,[],[f454])).

fof(f483,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl8_71 ),
    inference(avatar_component_clause,[],[f482])).

fof(f484,plain,
    ( spl8_71
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(avatar_split_clause,[],[f475,f464,f117,f109,f105,f101,f482])).

fof(f101,plain,
    ( spl8_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f105,plain,
    ( spl8_4
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f109,plain,
    ( spl8_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f117,plain,
    ( spl8_7
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f464,plain,
    ( spl8_68
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).

fof(f475,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | spl8_3
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f474,f102])).

fof(f102,plain,
    ( ~ v1_xboole_0(sK1)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f474,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f473,f110])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f109])).

fof(f473,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl8_4
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(subsumption_resolution,[],[f472,f106])).

fof(f106,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f472,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl8_7
    | ~ spl8_68 ),
    inference(superposition,[],[f118,f465])).

fof(f465,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl8_68 ),
    inference(avatar_component_clause,[],[f464])).

fof(f118,plain,
    ( ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f117])).

fof(f466,plain,
    ( spl8_68
    | ~ spl8_1
    | ~ spl8_57 ),
    inference(avatar_split_clause,[],[f372,f369,f93,f464])).

fof(f369,plain,
    ( spl8_57
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).

fof(f372,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) )
    | ~ spl8_1
    | ~ spl8_57 ),
    inference(resolution,[],[f370,f94])).

fof(f370,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) )
    | ~ spl8_57 ),
    inference(avatar_component_clause,[],[f369])).

fof(f456,plain,
    ( ~ spl8_40
    | spl8_67
    | ~ spl8_1
    | ~ spl8_51
    | ~ spl8_63 ),
    inference(avatar_split_clause,[],[f417,f404,f334,f93,f454,f274])).

fof(f334,plain,
    ( spl8_51
  <=> ! [X1,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f417,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_relat_1(sK3) )
    | ~ spl8_1
    | ~ spl8_51
    | ~ spl8_63 ),
    inference(forward_demodulation,[],[f415,f405])).

fof(f415,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_relat_1(sK3)
        | ~ r2_hidden(k1_funct_1(sK3,sK7(k1_relat_1(sK3),X0,sK3)),X0) )
    | ~ spl8_1
    | ~ spl8_51
    | ~ spl8_63 ),
    inference(backward_demodulation,[],[f348,f405])).

fof(f348,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK3)
        | ~ r2_hidden(k1_funct_1(sK3,sK7(k1_relat_1(sK3),X0,sK3)),X0)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) )
    | ~ spl8_1
    | ~ spl8_51 ),
    inference(resolution,[],[f335,f94])).

fof(f335,plain,
    ( ! [X2,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) )
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f334])).

fof(f414,plain,
    ( ~ spl8_5
    | ~ spl8_9
    | spl8_50
    | ~ spl8_61 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_9
    | spl8_50
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f412,f331])).

fof(f331,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | spl8_50 ),
    inference(avatar_component_clause,[],[f330])).

fof(f330,plain,
    ( spl8_50
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f412,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_5
    | ~ spl8_9
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f409,f126])).

fof(f126,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl8_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f409,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl8_5
    | ~ spl8_61 ),
    inference(backward_demodulation,[],[f110,f388])).

fof(f388,plain,
    ( k1_xboole_0 = sK2
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl8_61
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f406,plain,
    ( spl8_63
    | ~ spl8_5
    | ~ spl8_27
    | ~ spl8_60 ),
    inference(avatar_split_clause,[],[f394,f384,f207,f109,f404])).

fof(f207,plain,
    ( spl8_27
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f384,plain,
    ( spl8_60
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f394,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl8_5
    | ~ spl8_27
    | ~ spl8_60 ),
    inference(subsumption_resolution,[],[f390,f110])).

fof(f390,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_27
    | ~ spl8_60 ),
    inference(superposition,[],[f385,f208])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f207])).

fof(f385,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f384])).

fof(f389,plain,
    ( spl8_60
    | spl8_61
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_48 ),
    inference(avatar_split_clause,[],[f346,f318,f109,f105,f387,f384])).

fof(f318,plain,
    ( spl8_48
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f346,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl8_4
    | ~ spl8_5
    | ~ spl8_48 ),
    inference(subsumption_resolution,[],[f345,f110])).

fof(f345,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl8_4
    | ~ spl8_48 ),
    inference(resolution,[],[f319,f106])).

fof(f319,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f318])).

fof(f371,plain,(
    spl8_57 ),
    inference(avatar_split_clause,[],[f72,f369])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f336,plain,(
    spl8_51 ),
    inference(avatar_split_clause,[],[f86,f334])).

fof(f86,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f332,plain,
    ( ~ spl8_50
    | ~ spl8_10
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f323,f314,f129,f330])).

fof(f129,plain,
    ( spl8_10
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f323,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl8_10
    | ~ spl8_47 ),
    inference(superposition,[],[f315,f130])).

fof(f130,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f129])).

fof(f327,plain,(
    spl8_49 ),
    inference(avatar_split_clause,[],[f87,f325])).

fof(f87,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK7(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f320,plain,(
    spl8_48 ),
    inference(avatar_split_clause,[],[f67,f318])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f316,plain,
    ( spl8_47
    | ~ spl8_20
    | spl8_39 ),
    inference(avatar_split_clause,[],[f280,f271,f174,f314])).

fof(f174,plain,
    ( spl8_20
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f271,plain,
    ( spl8_39
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f280,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl8_20
    | spl8_39 ),
    inference(resolution,[],[f272,f175])).

fof(f175,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f174])).

fof(f272,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl8_39 ),
    inference(avatar_component_clause,[],[f271])).

fof(f279,plain,
    ( ~ spl8_5
    | ~ spl8_8
    | ~ spl8_15
    | spl8_40 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl8_5
    | ~ spl8_8
    | ~ spl8_15
    | spl8_40 ),
    inference(unit_resulting_resolution,[],[f122,f110,f275,f152])).

fof(f152,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f151,plain,
    ( spl8_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f275,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_40 ),
    inference(avatar_component_clause,[],[f274])).

fof(f122,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl8_8
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f276,plain,
    ( ~ spl8_39
    | ~ spl8_40
    | ~ spl8_17
    | spl8_37 ),
    inference(avatar_split_clause,[],[f264,f261,f160,f274,f271])).

fof(f160,plain,
    ( spl8_17
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f261,plain,
    ( spl8_37
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f264,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl8_17
    | spl8_37 ),
    inference(resolution,[],[f262,f161])).

fof(f161,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1)
        | ~ v5_relat_1(X1,X0) )
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f262,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl8_37 ),
    inference(avatar_component_clause,[],[f261])).

fof(f263,plain,
    ( ~ spl8_37
    | ~ spl8_5
    | spl8_6
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f259,f215,f113,f109,f261])).

fof(f113,plain,
    ( spl8_6
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f215,plain,
    ( spl8_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f259,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ spl8_5
    | spl8_6
    | ~ spl8_29 ),
    inference(backward_demodulation,[],[f114,f249])).

fof(f249,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)
    | ~ spl8_5
    | ~ spl8_29 ),
    inference(resolution,[],[f216,f110])).

fof(f216,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f215])).

fof(f114,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl8_6 ),
    inference(avatar_component_clause,[],[f113])).

fof(f217,plain,(
    spl8_29 ),
    inference(avatar_split_clause,[],[f59,f215])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f209,plain,(
    spl8_27 ),
    inference(avatar_split_clause,[],[f58,f207])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f176,plain,(
    spl8_20 ),
    inference(avatar_split_clause,[],[f61,f174])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f162,plain,(
    spl8_17 ),
    inference(avatar_split_clause,[],[f50,f160])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f153,plain,(
    spl8_15 ),
    inference(avatar_split_clause,[],[f41,f151])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f135,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f51,f133])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f131,plain,(
    spl8_10 ),
    inference(avatar_split_clause,[],[f78,f129])).

fof(f78,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f127,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f77,f125])).

fof(f77,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f123,plain,(
    spl8_8 ),
    inference(avatar_split_clause,[],[f48,f121])).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f119,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f34,f117])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r1_tarski(k2_relset_1(X1,X2,X3),X0)
              & ! [X4] :
                  ( r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)
                  | ~ m1_subset_1(X4,X1) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X3,X1,X2)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X3,X1,X2)
                  & v1_funct_1(X3) )
               => ( ! [X4] :
                      ( m1_subset_1(X4,X1)
                     => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
                 => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_2(X3,X1,X2)
                & v1_funct_1(X3) )
             => ( ! [X4] :
                    ( m1_subset_1(X4,X1)
                   => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) )
               => r1_tarski(k2_relset_1(X1,X2,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).

fof(f115,plain,(
    ~ spl8_6 ),
    inference(avatar_split_clause,[],[f38,f113])).

fof(f38,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f111,plain,(
    spl8_5 ),
    inference(avatar_split_clause,[],[f37,f109])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f107,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f36,f105])).

fof(f36,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f103,plain,(
    ~ spl8_3 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f35,f93])).

fof(f35,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:46:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (3575)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.43  % (3583)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (3579)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (3571)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (3585)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (3571)Refutation not found, incomplete strategy% (3571)------------------------------
% 0.20/0.49  % (3571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3577)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (3579)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (3571)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3571)Memory used [KB]: 10618
% 0.20/0.50  % (3571)Time elapsed: 0.066 s
% 0.20/0.50  % (3571)------------------------------
% 0.20/0.50  % (3571)------------------------------
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f714,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f95,f103,f107,f111,f115,f119,f123,f127,f131,f135,f153,f162,f176,f209,f217,f263,f276,f279,f316,f320,f327,f332,f336,f371,f389,f406,f414,f456,f466,f484,f500,f517,f705,f712])).
% 0.20/0.51  fof(f712,plain,(
% 0.20/0.51    ~spl8_47 | spl8_76 | ~spl8_108),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f711])).
% 0.20/0.51  fof(f711,plain,(
% 0.20/0.51    $false | (~spl8_47 | spl8_76 | ~spl8_108)),
% 0.20/0.51    inference(subsumption_resolution,[],[f707,f315])).
% 0.20/0.51  fof(f315,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | ~spl8_47),
% 0.20/0.51    inference(avatar_component_clause,[],[f314])).
% 0.20/0.51  fof(f314,plain,(
% 0.20/0.51    spl8_47 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 0.20/0.51  fof(f707,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl8_76 | ~spl8_108)),
% 0.20/0.51    inference(resolution,[],[f704,f516])).
% 0.20/0.51  fof(f516,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK1,sK0,sK3),sK1) | spl8_76),
% 0.20/0.51    inference(avatar_component_clause,[],[f515])).
% 0.20/0.51  fof(f515,plain,(
% 0.20/0.51    spl8_76 <=> r2_hidden(sK7(sK1,sK0,sK3),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_76])])).
% 0.20/0.51  fof(f704,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK7(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl8_108),
% 0.20/0.51    inference(avatar_component_clause,[],[f703])).
% 0.20/0.51  fof(f703,plain,(
% 0.20/0.51    spl8_108 <=> ! [X0] : (r2_hidden(sK7(sK1,X0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_108])])).
% 0.20/0.51  fof(f705,plain,(
% 0.20/0.51    ~spl8_40 | spl8_108 | ~spl8_1 | ~spl8_49 | ~spl8_63),
% 0.20/0.51    inference(avatar_split_clause,[],[f424,f404,f325,f93,f703,f274])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    spl8_40 <=> v1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl8_1 <=> v1_funct_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    spl8_49 <=> ! [X1,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.20/0.51  fof(f404,plain,(
% 0.20/0.51    spl8_63 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_63])])).
% 0.20/0.51  fof(f424,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK7(sK1,X0,sK3),sK1) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl8_1 | ~spl8_49 | ~spl8_63)),
% 0.20/0.51    inference(subsumption_resolution,[],[f420,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    v1_funct_1(sK3) | ~spl8_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f420,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(sK7(sK1,X0,sK3),sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | (~spl8_49 | ~spl8_63)),
% 0.20/0.51    inference(superposition,[],[f326,f405])).
% 0.20/0.51  fof(f405,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | ~spl8_63),
% 0.20/0.51    inference(avatar_component_clause,[],[f404])).
% 0.20/0.51  fof(f326,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) ) | ~spl8_49),
% 0.20/0.51    inference(avatar_component_clause,[],[f325])).
% 0.20/0.51  fof(f517,plain,(
% 0.20/0.51    ~spl8_76 | ~spl8_11 | spl8_74),
% 0.20/0.51    inference(avatar_split_clause,[],[f505,f498,f133,f515])).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl8_11 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.20/0.51  fof(f498,plain,(
% 0.20/0.51    spl8_74 <=> m1_subset_1(sK7(sK1,sK0,sK3),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_74])])).
% 0.20/0.51  fof(f505,plain,(
% 0.20/0.51    ~r2_hidden(sK7(sK1,sK0,sK3),sK1) | (~spl8_11 | spl8_74)),
% 0.20/0.51    inference(resolution,[],[f499,f134])).
% 0.20/0.51  fof(f134,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl8_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f133])).
% 0.20/0.51  fof(f499,plain,(
% 0.20/0.51    ~m1_subset_1(sK7(sK1,sK0,sK3),sK1) | spl8_74),
% 0.20/0.51    inference(avatar_component_clause,[],[f498])).
% 0.20/0.51  fof(f500,plain,(
% 0.20/0.51    ~spl8_74 | ~spl8_47 | ~spl8_67 | ~spl8_71),
% 0.20/0.51    inference(avatar_split_clause,[],[f490,f482,f454,f314,f498])).
% 0.20/0.51  fof(f454,plain,(
% 0.20/0.51    spl8_67 <=> ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_67])])).
% 0.20/0.51  fof(f482,plain,(
% 0.20/0.51    spl8_71 <=> ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_71])])).
% 0.20/0.51  fof(f490,plain,(
% 0.20/0.51    ~m1_subset_1(sK7(sK1,sK0,sK3),sK1) | (~spl8_47 | ~spl8_67 | ~spl8_71)),
% 0.20/0.51    inference(subsumption_resolution,[],[f489,f315])).
% 0.20/0.51  fof(f489,plain,(
% 0.20/0.51    ~m1_subset_1(sK7(sK1,sK0,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl8_67 | ~spl8_71)),
% 0.20/0.51    inference(resolution,[],[f483,f455])).
% 0.20/0.51  fof(f455,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))) ) | ~spl8_67),
% 0.20/0.51    inference(avatar_component_clause,[],[f454])).
% 0.20/0.51  fof(f483,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | ~spl8_71),
% 0.20/0.51    inference(avatar_component_clause,[],[f482])).
% 0.20/0.51  fof(f484,plain,(
% 0.20/0.51    spl8_71 | spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_68),
% 0.20/0.51    inference(avatar_split_clause,[],[f475,f464,f117,f109,f105,f101,f482])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl8_3 <=> v1_xboole_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl8_4 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl8_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl8_7 <=> ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.51  fof(f464,plain,(
% 0.20/0.51    spl8_68 <=> ! [X1,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_68])])).
% 0.20/0.51  fof(f475,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | (spl8_3 | ~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f474,f102])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1) | spl8_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f101])).
% 0.20/0.51  fof(f474,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl8_4 | ~spl8_5 | ~spl8_7 | ~spl8_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f473,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl8_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f109])).
% 0.20/0.51  fof(f473,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | (~spl8_4 | ~spl8_7 | ~spl8_68)),
% 0.20/0.51    inference(subsumption_resolution,[],[f472,f106])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl8_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f105])).
% 0.20/0.51  fof(f472,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | (~spl8_7 | ~spl8_68)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f471])).
% 0.20/0.51  fof(f471,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl8_7 | ~spl8_68)),
% 0.20/0.51    inference(superposition,[],[f118,f465])).
% 0.20/0.51  fof(f465,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) ) | ~spl8_68),
% 0.20/0.51    inference(avatar_component_clause,[],[f464])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) ) | ~spl8_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f466,plain,(
% 0.20/0.51    spl8_68 | ~spl8_1 | ~spl8_57),
% 0.20/0.51    inference(avatar_split_clause,[],[f372,f369,f93,f464])).
% 0.20/0.51  fof(f369,plain,(
% 0.20/0.51    spl8_57 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_57])])).
% 0.20/0.51  fof(f372,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)) ) | (~spl8_1 | ~spl8_57)),
% 0.20/0.51    inference(resolution,[],[f370,f94])).
% 0.20/0.51  fof(f370,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) ) | ~spl8_57),
% 0.20/0.51    inference(avatar_component_clause,[],[f369])).
% 0.20/0.51  fof(f456,plain,(
% 0.20/0.51    ~spl8_40 | spl8_67 | ~spl8_1 | ~spl8_51 | ~spl8_63),
% 0.20/0.51    inference(avatar_split_clause,[],[f417,f404,f334,f93,f454,f274])).
% 0.20/0.51  fof(f334,plain,(
% 0.20/0.51    spl8_51 <=> ! [X1,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.20/0.51  fof(f417,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(k1_funct_1(sK3,sK7(sK1,X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_relat_1(sK3)) ) | (~spl8_1 | ~spl8_51 | ~spl8_63)),
% 0.20/0.51    inference(forward_demodulation,[],[f415,f405])).
% 0.20/0.51  fof(f415,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_relat_1(sK3) | ~r2_hidden(k1_funct_1(sK3,sK7(k1_relat_1(sK3),X0,sK3)),X0)) ) | (~spl8_1 | ~spl8_51 | ~spl8_63)),
% 0.20/0.51    inference(backward_demodulation,[],[f348,f405])).
% 0.20/0.51  fof(f348,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_relat_1(sK3) | ~r2_hidden(k1_funct_1(sK3,sK7(k1_relat_1(sK3),X0,sK3)),X0) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))) ) | (~spl8_1 | ~spl8_51)),
% 0.20/0.51    inference(resolution,[],[f335,f94])).
% 0.20/0.51  fof(f335,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) ) | ~spl8_51),
% 0.20/0.51    inference(avatar_component_clause,[],[f334])).
% 0.20/0.51  fof(f414,plain,(
% 0.20/0.51    ~spl8_5 | ~spl8_9 | spl8_50 | ~spl8_61),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f413])).
% 0.20/0.51  fof(f413,plain,(
% 0.20/0.51    $false | (~spl8_5 | ~spl8_9 | spl8_50 | ~spl8_61)),
% 0.20/0.51    inference(subsumption_resolution,[],[f412,f331])).
% 0.20/0.51  fof(f331,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | spl8_50),
% 0.20/0.51    inference(avatar_component_clause,[],[f330])).
% 0.20/0.51  fof(f330,plain,(
% 0.20/0.51    spl8_50 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.20/0.51  fof(f412,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_5 | ~spl8_9 | ~spl8_61)),
% 0.20/0.51    inference(forward_demodulation,[],[f409,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl8_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f125])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    spl8_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.20/0.51  fof(f409,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl8_5 | ~spl8_61)),
% 0.20/0.51    inference(backward_demodulation,[],[f110,f388])).
% 0.20/0.51  fof(f388,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl8_61),
% 0.20/0.51    inference(avatar_component_clause,[],[f387])).
% 0.20/0.51  fof(f387,plain,(
% 0.20/0.51    spl8_61 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 0.20/0.51  fof(f406,plain,(
% 0.20/0.51    spl8_63 | ~spl8_5 | ~spl8_27 | ~spl8_60),
% 0.20/0.51    inference(avatar_split_clause,[],[f394,f384,f207,f109,f404])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl8_27 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.20/0.51  fof(f384,plain,(
% 0.20/0.51    spl8_60 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 0.20/0.51  fof(f394,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | (~spl8_5 | ~spl8_27 | ~spl8_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f390,f110])).
% 0.20/0.51  fof(f390,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl8_27 | ~spl8_60)),
% 0.20/0.51    inference(superposition,[],[f385,f208])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_27),
% 0.20/0.51    inference(avatar_component_clause,[],[f207])).
% 0.20/0.51  fof(f385,plain,(
% 0.20/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl8_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f384])).
% 0.20/0.51  fof(f389,plain,(
% 0.20/0.51    spl8_60 | spl8_61 | ~spl8_4 | ~spl8_5 | ~spl8_48),
% 0.20/0.51    inference(avatar_split_clause,[],[f346,f318,f109,f105,f387,f384])).
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    spl8_48 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 0.20/0.51  fof(f346,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl8_4 | ~spl8_5 | ~spl8_48)),
% 0.20/0.51    inference(subsumption_resolution,[],[f345,f110])).
% 0.20/0.51  fof(f345,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl8_4 | ~spl8_48)),
% 0.20/0.51    inference(resolution,[],[f319,f106])).
% 0.20/0.51  fof(f319,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_48),
% 0.20/0.51    inference(avatar_component_clause,[],[f318])).
% 0.20/0.51  fof(f371,plain,(
% 0.20/0.51    spl8_57),
% 0.20/0.51    inference(avatar_split_clause,[],[f72,f369])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.51  fof(f336,plain,(
% 0.20/0.51    spl8_51),
% 0.20/0.51    inference(avatar_split_clause,[],[f86,f334])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK7(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f69])).
% 0.20/0.51  fof(f69,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK7(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f30])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.51  fof(f332,plain,(
% 0.20/0.51    ~spl8_50 | ~spl8_10 | ~spl8_47),
% 0.20/0.51    inference(avatar_split_clause,[],[f323,f314,f129,f330])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl8_10 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.20/0.51  fof(f323,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl8_10 | ~spl8_47)),
% 0.20/0.51    inference(superposition,[],[f315,f130])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl8_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f129])).
% 0.20/0.51  fof(f327,plain,(
% 0.20/0.51    spl8_49),
% 0.20/0.51    inference(avatar_split_clause,[],[f87,f325])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(sK7(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f68])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK7(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f320,plain,(
% 0.20/0.51    spl8_48),
% 0.20/0.51    inference(avatar_split_clause,[],[f67,f318])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f316,plain,(
% 0.20/0.51    spl8_47 | ~spl8_20 | spl8_39),
% 0.20/0.51    inference(avatar_split_clause,[],[f280,f271,f174,f314])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    spl8_20 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.20/0.51  fof(f271,plain,(
% 0.20/0.51    spl8_39 <=> v5_relat_1(sK3,sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 0.20/0.51  fof(f280,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | (~spl8_20 | spl8_39)),
% 0.20/0.51    inference(resolution,[],[f272,f175])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl8_20),
% 0.20/0.51    inference(avatar_component_clause,[],[f174])).
% 0.20/0.51  fof(f272,plain,(
% 0.20/0.51    ~v5_relat_1(sK3,sK0) | spl8_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f271])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ~spl8_5 | ~spl8_8 | ~spl8_15 | spl8_40),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f277])).
% 0.20/0.51  fof(f277,plain,(
% 0.20/0.51    $false | (~spl8_5 | ~spl8_8 | ~spl8_15 | spl8_40)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f122,f110,f275,f152])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl8_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl8_15 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.20/0.51  fof(f275,plain,(
% 0.20/0.51    ~v1_relat_1(sK3) | spl8_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f274])).
% 0.20/0.51  fof(f122,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl8_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f121])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl8_8 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.51  fof(f276,plain,(
% 0.20/0.51    ~spl8_39 | ~spl8_40 | ~spl8_17 | spl8_37),
% 0.20/0.51    inference(avatar_split_clause,[],[f264,f261,f160,f274,f271])).
% 0.20/0.51  fof(f160,plain,(
% 0.20/0.51    spl8_17 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    spl8_37 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 0.20/0.51  fof(f264,plain,(
% 0.20/0.51    ~v1_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | (~spl8_17 | spl8_37)),
% 0.20/0.51    inference(resolution,[],[f262,f161])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0)) ) | ~spl8_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f160])).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK3),sK0) | spl8_37),
% 0.20/0.51    inference(avatar_component_clause,[],[f261])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    ~spl8_37 | ~spl8_5 | spl8_6 | ~spl8_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f259,f215,f113,f109,f261])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl8_6 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.51  fof(f215,plain,(
% 0.20/0.51    spl8_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    ~r1_tarski(k2_relat_1(sK3),sK0) | (~spl8_5 | spl8_6 | ~spl8_29)),
% 0.20/0.51    inference(backward_demodulation,[],[f114,f249])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) | (~spl8_5 | ~spl8_29)),
% 0.20/0.51    inference(resolution,[],[f216,f110])).
% 0.20/0.51  fof(f216,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl8_29),
% 0.20/0.51    inference(avatar_component_clause,[],[f215])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl8_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f113])).
% 0.20/0.51  fof(f217,plain,(
% 0.20/0.51    spl8_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f215])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f209,plain,(
% 0.20/0.51    spl8_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f207])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f176,plain,(
% 0.20/0.51    spl8_20),
% 0.20/0.51    inference(avatar_split_clause,[],[f61,f174])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    spl8_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f160])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl8_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f41,f151])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    spl8_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f133])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl8_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f78,f129])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    spl8_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f77,f125])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl8_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f121])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl8_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f117])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f15])).
% 0.20/0.51  fof(f15,conjecture,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    ~spl8_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f113])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl8_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f109])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl8_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f105])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    ~spl8_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f40,f101])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl8_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f35,f93])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (3579)------------------------------
% 0.20/0.51  % (3579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3579)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (3579)Memory used [KB]: 11001
% 0.20/0.51  % (3579)Time elapsed: 0.084 s
% 0.20/0.51  % (3579)------------------------------
% 0.20/0.51  % (3579)------------------------------
% 0.20/0.51  % (3569)Success in time 0.16 s
%------------------------------------------------------------------------------
