%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 307 expanded)
%              Number of leaves         :   47 ( 141 expanded)
%              Depth                    :    8
%              Number of atoms          :  611 (1060 expanded)
%              Number of equality atoms :   73 ( 107 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f717,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f87,f91,f95,f99,f103,f107,f111,f115,f119,f133,f137,f146,f171,f175,f183,f224,f255,f259,f262,f267,f288,f340,f353,f410,f423,f433,f449,f478,f497,f644,f673,f681,f702,f710,f716])).

fof(f716,plain,
    ( ~ spl5_64
    | ~ spl5_79
    | ~ spl5_84 ),
    inference(avatar_contradiction_clause,[],[f715])).

fof(f715,plain,
    ( $false
    | ~ spl5_64
    | ~ spl5_79
    | ~ spl5_84 ),
    inference(subsumption_resolution,[],[f712,f448])).

fof(f448,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f447])).

fof(f447,plain,
    ( spl5_64
  <=> ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f712,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_79
    | ~ spl5_84 ),
    inference(resolution,[],[f709,f680])).

fof(f680,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) )
    | ~ spl5_79 ),
    inference(avatar_component_clause,[],[f679])).

fof(f679,plain,
    ( spl5_79
  <=> ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).

fof(f709,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | ~ spl5_84 ),
    inference(avatar_component_clause,[],[f708])).

fof(f708,plain,
    ( spl5_84
  <=> r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).

fof(f710,plain,
    ( spl5_84
    | ~ spl5_64
    | ~ spl5_83 ),
    inference(avatar_split_clause,[],[f704,f700,f447,f708])).

fof(f700,plain,
    ( spl5_83
  <=> ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).

fof(f704,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)
    | ~ spl5_64
    | ~ spl5_83 ),
    inference(resolution,[],[f701,f448])).

fof(f701,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) )
    | ~ spl5_83 ),
    inference(avatar_component_clause,[],[f700])).

fof(f702,plain,
    ( spl5_83
    | ~ spl5_72
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f677,f671,f495,f700])).

fof(f495,plain,
    ( spl5_72
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f671,plain,
    ( spl5_78
  <=> ! [X3] :
        ( r2_hidden(sK4(sK1,X3,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f677,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0) )
    | ~ spl5_72
    | ~ spl5_78 ),
    inference(resolution,[],[f672,f496])).

fof(f496,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f495])).

fof(f672,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK1,X3,sK3),sK1)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) )
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f671])).

fof(f681,plain,
    ( ~ spl5_38
    | spl5_79
    | ~ spl5_1
    | ~ spl5_41
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f619,f338,f265,f77,f679,f249])).

fof(f249,plain,
    ( spl5_38
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f77,plain,
    ( spl5_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f265,plain,
    ( spl5_41
  <=> ! [X1,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f338,plain,
    ( spl5_51
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f619,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) )
    | ~ spl5_1
    | ~ spl5_41
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f612,f78])).

fof(f78,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f612,plain,
    ( ! [X4] :
        ( ~ r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))) )
    | ~ spl5_41
    | ~ spl5_51 ),
    inference(superposition,[],[f266,f339])).

fof(f339,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f338])).

fof(f266,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) )
    | ~ spl5_41 ),
    inference(avatar_component_clause,[],[f265])).

fof(f673,plain,
    ( ~ spl5_38
    | spl5_78
    | ~ spl5_1
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f618,f338,f257,f77,f671,f249])).

fof(f257,plain,
    ( spl5_40
  <=> ! [X1,X2] :
        ( ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f618,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK1,X3,sK3),sK1)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) )
    | ~ spl5_1
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(subsumption_resolution,[],[f611,f78])).

fof(f611,plain,
    ( ! [X3] :
        ( r2_hidden(sK4(sK1,X3,sK3),sK1)
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3)
        | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))) )
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(superposition,[],[f258,f339])).

fof(f258,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
        | ~ v1_funct_1(X2)
        | ~ v1_relat_1(X2)
        | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f257])).

fof(f644,plain,
    ( ~ spl5_43
    | ~ spl5_10
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f457,f447,f113,f274])).

fof(f274,plain,
    ( spl5_43
  <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f113,plain,
    ( spl5_10
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f457,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_10
    | ~ spl5_64 ),
    inference(superposition,[],[f448,f114])).

fof(f114,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f497,plain,
    ( spl5_72
    | ~ spl5_11
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f479,f476,f117,f495])).

fof(f117,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | m1_subset_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f476,plain,
    ( spl5_68
  <=> ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f479,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl5_11
    | ~ spl5_68 ),
    inference(resolution,[],[f477,f118])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f477,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | r2_hidden(k1_funct_1(sK3,X0),sK0) )
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f476])).

fof(f478,plain,
    ( spl5_68
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f429,f421,f101,f93,f89,f85,f476])).

fof(f85,plain,
    ( spl5_3
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f89,plain,
    ( spl5_4
  <=> v1_funct_2(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f93,plain,
    ( spl5_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f101,plain,
    ( spl5_7
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,sK1)
        | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f421,plain,
    ( spl5_60
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f429,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1) )
    | spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f428,f86])).

fof(f86,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f428,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f427,f94])).

fof(f94,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f427,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl5_4
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f426,f90])).

fof(f90,plain,
    ( v1_funct_2(sK3,sK1,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f426,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | v1_xboole_0(sK1) )
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(duplicate_literal_removal,[],[f425])).

fof(f425,plain,
    ( ! [X0] :
        ( r2_hidden(k1_funct_1(sK3,X0),sK0)
        | ~ m1_subset_1(X0,sK1)
        | ~ v1_funct_2(sK3,sK1,sK2)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
        | ~ m1_subset_1(X0,sK1)
        | v1_xboole_0(sK1) )
    | ~ spl5_7
    | ~ spl5_60 ),
    inference(superposition,[],[f102,f422])).

fof(f422,plain,
    ( ! [X2,X0,X1] :
        ( k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | v1_xboole_0(X0) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f421])).

fof(f102,plain,
    ( ! [X4] :
        ( r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)
        | ~ m1_subset_1(X4,sK1) )
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f449,plain,
    ( spl5_64
    | spl5_32
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f438,f431,f222,f447])).

fof(f222,plain,
    ( spl5_32
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f431,plain,
    ( spl5_61
  <=> ! [X1,X0,X2] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f438,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl5_32
    | ~ spl5_61 ),
    inference(resolution,[],[f432,f223])).

fof(f223,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | spl5_32 ),
    inference(avatar_component_clause,[],[f222])).

fof(f432,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f431])).

fof(f433,plain,
    ( spl5_61
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f208,f181,f173,f431])).

fof(f173,plain,
    ( spl5_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f181,plain,
    ( spl5_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f208,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_23
    | ~ spl5_25 ),
    inference(superposition,[],[f182,f174])).

fof(f174,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f182,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f423,plain,
    ( spl5_60
    | ~ spl5_1
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f291,f286,f77,f421])).

fof(f286,plain,
    ( spl5_45
  <=> ! [X1,X3,X0,X2] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f291,plain,
    ( ! [X2,X0,X1] :
        ( v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,X0,X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X2,X0)
        | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) )
    | ~ spl5_1
    | ~ spl5_45 ),
    inference(resolution,[],[f287,f78])).

fof(f287,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v1_funct_1(X2)
        | v1_xboole_0(X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ m1_subset_1(X3,X0)
        | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f286])).

fof(f410,plain,
    ( spl5_46
    | spl5_47
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f341,f253,f93,f89,f296,f293])).

fof(f293,plain,
    ( spl5_46
  <=> sK1 = k1_relset_1(sK1,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f296,plain,
    ( spl5_47
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f253,plain,
    ( spl5_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f341,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f325,f94])).

fof(f325,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_4
    | ~ spl5_39 ),
    inference(resolution,[],[f90,f254])).

fof(f254,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f253])).

fof(f353,plain,
    ( spl5_43
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f349,f296,f109,f93,f274])).

fof(f109,plain,
    ( spl5_9
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f349,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5
    | ~ spl5_9
    | ~ spl5_47 ),
    inference(forward_demodulation,[],[f344,f110])).

fof(f110,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f344,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl5_5
    | ~ spl5_47 ),
    inference(backward_demodulation,[],[f94,f297])).

fof(f297,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f296])).

fof(f340,plain,
    ( spl5_51
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f332,f293,f169,f93,f338])).

fof(f169,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f332,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_46 ),
    inference(subsumption_resolution,[],[f328,f94])).

fof(f328,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_22
    | ~ spl5_46 ),
    inference(superposition,[],[f294,f170])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f169])).

fof(f294,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK3)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f293])).

fof(f288,plain,(
    spl5_45 ),
    inference(avatar_split_clause,[],[f60,f286])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_xboole_0(X0)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f267,plain,(
    spl5_41 ),
    inference(avatar_split_clause,[],[f70,f265])).

fof(f70,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | ~ r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f262,plain,
    ( ~ spl5_5
    | ~ spl5_8
    | ~ spl5_15
    | spl5_38 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl5_5
    | ~ spl5_8
    | ~ spl5_15
    | spl5_38 ),
    inference(unit_resulting_resolution,[],[f106,f94,f250,f136])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f250,plain,
    ( ~ v1_relat_1(sK3)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f249])).

fof(f106,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl5_8
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f259,plain,(
    spl5_40 ),
    inference(avatar_split_clause,[],[f71,f257])).

fof(f71,plain,(
    ! [X2,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | k1_relat_1(X2) != X0
      | r2_hidden(sK4(X0,X1,X2),X0)
      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f255,plain,(
    spl5_39 ),
    inference(avatar_split_clause,[],[f55,f253])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f224,plain,
    ( ~ spl5_32
    | ~ spl5_5
    | spl5_17
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f205,f173,f144,f93,f222])).

fof(f144,plain,
    ( spl5_17
  <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f205,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ spl5_5
    | spl5_17
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f202,f94])).

fof(f202,plain,
    ( ~ m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | spl5_17
    | ~ spl5_23 ),
    inference(superposition,[],[f145,f174])).

fof(f145,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f183,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f49,f181])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f175,plain,(
    spl5_23 ),
    inference(avatar_split_clause,[],[f48,f173])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f171,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f47,f169])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f146,plain,
    ( ~ spl5_17
    | spl5_6
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f138,f131,f97,f144])).

fof(f97,plain,
    ( spl5_6
  <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f131,plain,
    ( spl5_14
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f138,plain,
    ( ~ m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))
    | spl5_6
    | ~ spl5_14 ),
    inference(resolution,[],[f132,f98])).

fof(f98,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) )
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f131])).

fof(f137,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f37,f135])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f133,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f43,f131])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f119,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f39,f117])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f115,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f62,f113])).

fof(f62,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
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

fof(f111,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f107,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f38,f105])).

fof(f38,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f103,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f30,f101])).

fof(f30,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,sK1)
      | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f99,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    ~ r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f91,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f32,f89])).

fof(f32,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f36,f85])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f79,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23914)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (23919)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (23928)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (23925)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (23923)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (23918)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (23925)Refutation not found, incomplete strategy% (23925)------------------------------
% 0.20/0.49  % (23925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (23925)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (23925)Memory used [KB]: 10618
% 0.20/0.49  % (23925)Time elapsed: 0.073 s
% 0.20/0.49  % (23925)------------------------------
% 0.20/0.49  % (23925)------------------------------
% 0.20/0.49  % (23929)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.49  % (23917)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (23915)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (23927)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.50  % (23915)Refutation not found, incomplete strategy% (23915)------------------------------
% 0.20/0.50  % (23915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (23915)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (23915)Memory used [KB]: 10618
% 0.20/0.50  % (23915)Time elapsed: 0.083 s
% 0.20/0.50  % (23915)------------------------------
% 0.20/0.50  % (23915)------------------------------
% 0.20/0.50  % (23916)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.50  % (23921)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (23930)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (23934)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (23934)Refutation not found, incomplete strategy% (23934)------------------------------
% 0.20/0.51  % (23934)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23934)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (23934)Memory used [KB]: 10618
% 0.20/0.51  % (23934)Time elapsed: 0.096 s
% 0.20/0.51  % (23934)------------------------------
% 0.20/0.51  % (23934)------------------------------
% 0.20/0.51  % (23933)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (23932)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.51  % (23920)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.51  % (23926)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (23923)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f717,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f79,f87,f91,f95,f99,f103,f107,f111,f115,f119,f133,f137,f146,f171,f175,f183,f224,f255,f259,f262,f267,f288,f340,f353,f410,f423,f433,f449,f478,f497,f644,f673,f681,f702,f710,f716])).
% 0.20/0.51  fof(f716,plain,(
% 0.20/0.51    ~spl5_64 | ~spl5_79 | ~spl5_84),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f715])).
% 0.20/0.51  fof(f715,plain,(
% 0.20/0.51    $false | (~spl5_64 | ~spl5_79 | ~spl5_84)),
% 0.20/0.51    inference(subsumption_resolution,[],[f712,f448])).
% 0.20/0.51  fof(f448,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | ~spl5_64),
% 0.20/0.51    inference(avatar_component_clause,[],[f447])).
% 0.20/0.51  fof(f447,plain,(
% 0.20/0.51    spl5_64 <=> ! [X0] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 0.20/0.51  fof(f712,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_79 | ~spl5_84)),
% 0.20/0.51    inference(resolution,[],[f709,f680])).
% 0.20/0.51  fof(f680,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4)))) ) | ~spl5_79),
% 0.20/0.51    inference(avatar_component_clause,[],[f679])).
% 0.20/0.51  fof(f679,plain,(
% 0.20/0.51    spl5_79 <=> ! [X4] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_79])])).
% 0.20/0.51  fof(f709,plain,(
% 0.20/0.51    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | ~spl5_84),
% 0.20/0.51    inference(avatar_component_clause,[],[f708])).
% 0.20/0.51  fof(f708,plain,(
% 0.20/0.51    spl5_84 <=> r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_84])])).
% 0.20/0.51  fof(f710,plain,(
% 0.20/0.51    spl5_84 | ~spl5_64 | ~spl5_83),
% 0.20/0.51    inference(avatar_split_clause,[],[f704,f700,f447,f708])).
% 0.20/0.51  fof(f700,plain,(
% 0.20/0.51    spl5_83 <=> ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_83])])).
% 0.20/0.51  fof(f704,plain,(
% 0.20/0.51    r2_hidden(k1_funct_1(sK3,sK4(sK1,sK0,sK3)),sK0) | (~spl5_64 | ~spl5_83)),
% 0.20/0.51    inference(resolution,[],[f701,f448])).
% 0.20/0.51  fof(f701,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)) ) | ~spl5_83),
% 0.20/0.51    inference(avatar_component_clause,[],[f700])).
% 0.20/0.51  fof(f702,plain,(
% 0.20/0.51    spl5_83 | ~spl5_72 | ~spl5_78),
% 0.20/0.51    inference(avatar_split_clause,[],[f677,f671,f495,f700])).
% 0.20/0.51  fof(f495,plain,(
% 0.20/0.51    spl5_72 <=> ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 0.20/0.51  fof(f671,plain,(
% 0.20/0.51    spl5_78 <=> ! [X3] : (r2_hidden(sK4(sK1,X3,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 0.20/0.51  fof(f677,plain,(
% 0.20/0.51    ( ! [X0] : (m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | r2_hidden(k1_funct_1(sK3,sK4(sK1,X0,sK3)),sK0)) ) | (~spl5_72 | ~spl5_78)),
% 0.20/0.51    inference(resolution,[],[f672,f496])).
% 0.20/0.51  fof(f496,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_72),
% 0.20/0.51    inference(avatar_component_clause,[],[f495])).
% 0.20/0.51  fof(f672,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK4(sK1,X3,sK3),sK1) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))) ) | ~spl5_78),
% 0.20/0.51    inference(avatar_component_clause,[],[f671])).
% 0.20/0.51  fof(f681,plain,(
% 0.20/0.51    ~spl5_38 | spl5_79 | ~spl5_1 | ~spl5_41 | ~spl5_51),
% 0.20/0.51    inference(avatar_split_clause,[],[f619,f338,f265,f77,f679,f249])).
% 0.20/0.51  fof(f249,plain,(
% 0.20/0.51    spl5_38 <=> v1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    spl5_1 <=> v1_funct_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f265,plain,(
% 0.20/0.51    spl5_41 <=> ! [X1,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 0.20/0.51  fof(f338,plain,(
% 0.20/0.51    spl5_51 <=> sK1 = k1_relat_1(sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.20/0.51  fof(f619,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4)))) ) | (~spl5_1 | ~spl5_41 | ~spl5_51)),
% 0.20/0.51    inference(subsumption_resolution,[],[f612,f78])).
% 0.20/0.51  fof(f78,plain,(
% 0.20/0.51    v1_funct_1(sK3) | ~spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f77])).
% 0.20/0.51  fof(f612,plain,(
% 0.20/0.51    ( ! [X4] : (~r2_hidden(k1_funct_1(sK3,sK4(sK1,X4,sK3)),X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X4)))) ) | (~spl5_41 | ~spl5_51)),
% 0.20/0.51    inference(superposition,[],[f266,f339])).
% 0.20/0.51  fof(f339,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | ~spl5_51),
% 0.20/0.51    inference(avatar_component_clause,[],[f338])).
% 0.20/0.51  fof(f266,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) ) | ~spl5_41),
% 0.20/0.51    inference(avatar_component_clause,[],[f265])).
% 0.20/0.51  fof(f673,plain,(
% 0.20/0.51    ~spl5_38 | spl5_78 | ~spl5_1 | ~spl5_40 | ~spl5_51),
% 0.20/0.51    inference(avatar_split_clause,[],[f618,f338,f257,f77,f671,f249])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    spl5_40 <=> ! [X1,X2] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.20/0.51  fof(f618,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK4(sK1,X3,sK3),sK1) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))) ) | (~spl5_1 | ~spl5_40 | ~spl5_51)),
% 0.20/0.51    inference(subsumption_resolution,[],[f611,f78])).
% 0.20/0.51  fof(f611,plain,(
% 0.20/0.51    ( ! [X3] : (r2_hidden(sK4(sK1,X3,sK3),sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X3)))) ) | (~spl5_40 | ~spl5_51)),
% 0.20/0.51    inference(superposition,[],[f258,f339])).
% 0.20/0.51  fof(f258,plain,(
% 0.20/0.51    ( ! [X2,X1] : (r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) ) | ~spl5_40),
% 0.20/0.51    inference(avatar_component_clause,[],[f257])).
% 0.20/0.51  fof(f644,plain,(
% 0.20/0.51    ~spl5_43 | ~spl5_10 | ~spl5_64),
% 0.20/0.51    inference(avatar_split_clause,[],[f457,f447,f113,f274])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    spl5_43 <=> m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    spl5_10 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.20/0.51  fof(f457,plain,(
% 0.20/0.51    ~m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_10 | ~spl5_64)),
% 0.20/0.51    inference(superposition,[],[f448,f114])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl5_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f113])).
% 0.20/0.51  fof(f497,plain,(
% 0.20/0.51    spl5_72 | ~spl5_11 | ~spl5_68),
% 0.20/0.51    inference(avatar_split_clause,[],[f479,f476,f117,f495])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    spl5_11 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.20/0.51  fof(f476,plain,(
% 0.20/0.51    spl5_68 <=> ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.20/0.51  fof(f479,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~r2_hidden(X0,sK1)) ) | (~spl5_11 | ~spl5_68)),
% 0.20/0.51    inference(resolution,[],[f477,f118])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) ) | ~spl5_11),
% 0.20/0.51    inference(avatar_component_clause,[],[f117])).
% 0.20/0.51  fof(f477,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(X0,sK1) | r2_hidden(k1_funct_1(sK3,X0),sK0)) ) | ~spl5_68),
% 0.20/0.51    inference(avatar_component_clause,[],[f476])).
% 0.20/0.51  fof(f478,plain,(
% 0.20/0.51    spl5_68 | spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_60),
% 0.20/0.51    inference(avatar_split_clause,[],[f429,f421,f101,f93,f89,f85,f476])).
% 0.20/0.51  fof(f85,plain,(
% 0.20/0.51    spl5_3 <=> v1_xboole_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    spl5_4 <=> v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    spl5_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    spl5_7 <=> ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.20/0.51  fof(f421,plain,(
% 0.20/0.51    spl5_60 <=> ! [X1,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.20/0.51  fof(f429,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1)) ) | (spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f428,f86])).
% 0.20/0.51  fof(f86,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1) | spl5_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f85])).
% 0.20/0.51  fof(f428,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl5_4 | ~spl5_5 | ~spl5_7 | ~spl5_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f427,f94])).
% 0.20/0.51  fof(f94,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_5),
% 0.20/0.51    inference(avatar_component_clause,[],[f93])).
% 0.20/0.51  fof(f427,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | (~spl5_4 | ~spl5_7 | ~spl5_60)),
% 0.20/0.51    inference(subsumption_resolution,[],[f426,f90])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK1,sK2) | ~spl5_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f89])).
% 0.20/0.51  fof(f426,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | v1_xboole_0(sK1)) ) | (~spl5_7 | ~spl5_60)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f425])).
% 0.20/0.51  fof(f425,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(k1_funct_1(sK3,X0),sK0) | ~m1_subset_1(X0,sK1) | ~v1_funct_2(sK3,sK1,sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~m1_subset_1(X0,sK1) | v1_xboole_0(sK1)) ) | (~spl5_7 | ~spl5_60)),
% 0.20/0.51    inference(superposition,[],[f102,f422])).
% 0.20/0.51  fof(f422,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | v1_xboole_0(X0)) ) | ~spl5_60),
% 0.20/0.51    inference(avatar_component_clause,[],[f421])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    ( ! [X4] : (r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0) | ~m1_subset_1(X4,sK1)) ) | ~spl5_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f101])).
% 0.20/0.51  fof(f449,plain,(
% 0.20/0.51    spl5_64 | spl5_32 | ~spl5_61),
% 0.20/0.51    inference(avatar_split_clause,[],[f438,f431,f222,f447])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    spl5_32 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.20/0.51  fof(f431,plain,(
% 0.20/0.51    spl5_61 <=> ! [X1,X0,X2] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.20/0.51  fof(f438,plain,(
% 0.20/0.51    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | (spl5_32 | ~spl5_61)),
% 0.20/0.51    inference(resolution,[],[f432,f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | spl5_32),
% 0.20/0.51    inference(avatar_component_clause,[],[f222])).
% 0.20/0.51  fof(f432,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_61),
% 0.20/0.51    inference(avatar_component_clause,[],[f431])).
% 0.20/0.51  fof(f433,plain,(
% 0.20/0.51    spl5_61 | ~spl5_23 | ~spl5_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f208,f181,f173,f431])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    spl5_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.20/0.51  fof(f181,plain,(
% 0.20/0.51    spl5_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_23 | ~spl5_25)),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f207])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | (~spl5_23 | ~spl5_25)),
% 0.20/0.51    inference(superposition,[],[f182,f174])).
% 0.20/0.51  fof(f174,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_23),
% 0.20/0.51    inference(avatar_component_clause,[],[f173])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_25),
% 0.20/0.51    inference(avatar_component_clause,[],[f181])).
% 0.20/0.51  fof(f423,plain,(
% 0.20/0.51    spl5_60 | ~spl5_1 | ~spl5_45),
% 0.20/0.51    inference(avatar_split_clause,[],[f291,f286,f77,f421])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    spl5_45 <=> ! [X1,X3,X0,X2] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.20/0.51  fof(f291,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v1_xboole_0(X0) | ~v1_funct_2(sK3,X0,X1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,X0) | k3_funct_2(X0,X1,sK3,X2) = k1_funct_1(sK3,X2)) ) | (~spl5_1 | ~spl5_45)),
% 0.20/0.51    inference(resolution,[],[f287,f78])).
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | v1_xboole_0(X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) ) | ~spl5_45),
% 0.20/0.51    inference(avatar_component_clause,[],[f286])).
% 0.20/0.51  fof(f410,plain,(
% 0.20/0.51    spl5_46 | spl5_47 | ~spl5_4 | ~spl5_5 | ~spl5_39),
% 0.20/0.51    inference(avatar_split_clause,[],[f341,f253,f93,f89,f296,f293])).
% 0.20/0.51  fof(f293,plain,(
% 0.20/0.51    spl5_46 <=> sK1 = k1_relset_1(sK1,sK2,sK3)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 0.20/0.51  fof(f296,plain,(
% 0.20/0.51    spl5_47 <=> k1_xboole_0 = sK2),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    spl5_39 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.20/0.51  fof(f341,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | (~spl5_4 | ~spl5_5 | ~spl5_39)),
% 0.20/0.51    inference(subsumption_resolution,[],[f325,f94])).
% 0.20/0.51  fof(f325,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_4 | ~spl5_39)),
% 0.20/0.51    inference(resolution,[],[f90,f254])).
% 0.20/0.51  fof(f254,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_39),
% 0.20/0.51    inference(avatar_component_clause,[],[f253])).
% 0.20/0.51  fof(f353,plain,(
% 0.20/0.51    spl5_43 | ~spl5_5 | ~spl5_9 | ~spl5_47),
% 0.20/0.51    inference(avatar_split_clause,[],[f349,f296,f109,f93,f274])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    spl5_9 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.20/0.51  fof(f349,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) | (~spl5_5 | ~spl5_9 | ~spl5_47)),
% 0.20/0.51    inference(forward_demodulation,[],[f344,f110])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl5_9),
% 0.20/0.51    inference(avatar_component_clause,[],[f109])).
% 0.20/0.51  fof(f344,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) | (~spl5_5 | ~spl5_47)),
% 0.20/0.51    inference(backward_demodulation,[],[f94,f297])).
% 0.20/0.51  fof(f297,plain,(
% 0.20/0.51    k1_xboole_0 = sK2 | ~spl5_47),
% 0.20/0.51    inference(avatar_component_clause,[],[f296])).
% 0.20/0.51  fof(f340,plain,(
% 0.20/0.51    spl5_51 | ~spl5_5 | ~spl5_22 | ~spl5_46),
% 0.20/0.51    inference(avatar_split_clause,[],[f332,f293,f169,f93,f338])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    spl5_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.20/0.51  fof(f332,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | (~spl5_5 | ~spl5_22 | ~spl5_46)),
% 0.20/0.51    inference(subsumption_resolution,[],[f328,f94])).
% 0.20/0.51  fof(f328,plain,(
% 0.20/0.51    sK1 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl5_22 | ~spl5_46)),
% 0.20/0.51    inference(superposition,[],[f294,f170])).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_22),
% 0.20/0.51    inference(avatar_component_clause,[],[f169])).
% 0.20/0.51  fof(f294,plain,(
% 0.20/0.51    sK1 = k1_relset_1(sK1,sK2,sK3) | ~spl5_46),
% 0.20/0.51    inference(avatar_component_clause,[],[f293])).
% 0.20/0.51  fof(f288,plain,(
% 0.20/0.51    spl5_45),
% 0.20/0.51    inference(avatar_split_clause,[],[f60,f286])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v1_xboole_0(X0) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.20/0.51  fof(f267,plain,(
% 0.20/0.51    spl5_41),
% 0.20/0.51    inference(avatar_split_clause,[],[f70,f265])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(k1_funct_1(X2,sK4(k1_relat_1(X2),X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | ~r2_hidden(k1_funct_1(X2,sK4(X0,X1,X2)),X1) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    ~spl5_5 | ~spl5_8 | ~spl5_15 | spl5_38),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f260])).
% 0.20/0.51  fof(f260,plain,(
% 0.20/0.51    $false | (~spl5_5 | ~spl5_8 | ~spl5_15 | spl5_38)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f106,f94,f250,f136])).
% 0.20/0.51  fof(f136,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl5_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f135])).
% 0.20/0.51  fof(f135,plain,(
% 0.20/0.51    spl5_15 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    ~v1_relat_1(sK3) | spl5_38),
% 0.20/0.51    inference(avatar_component_clause,[],[f249])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl5_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    spl5_8 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.20/0.51  fof(f259,plain,(
% 0.20/0.51    spl5_40),
% 0.20/0.51    inference(avatar_split_clause,[],[f71,f257])).
% 0.20/0.51  fof(f71,plain,(
% 0.20/0.51    ( ! [X2,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | r2_hidden(sK4(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X2),X1)))) )),
% 0.20/0.51    inference(equality_resolution,[],[f56])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | k1_relat_1(X2) != X0 | r2_hidden(sK4(X0,X1,X2),X0) | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f255,plain,(
% 0.20/0.51    spl5_39),
% 0.20/0.51    inference(avatar_split_clause,[],[f55,f253])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(flattening,[],[f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    ~spl5_32 | ~spl5_5 | spl5_17 | ~spl5_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f205,f173,f144,f93,f222])).
% 0.20/0.51  fof(f144,plain,(
% 0.20/0.51    spl5_17 <=> m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | (~spl5_5 | spl5_17 | ~spl5_23)),
% 0.20/0.51    inference(subsumption_resolution,[],[f202,f94])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    ~m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (spl5_17 | ~spl5_23)),
% 0.20/0.51    inference(superposition,[],[f145,f174])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | spl5_17),
% 0.20/0.51    inference(avatar_component_clause,[],[f144])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    spl5_25),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f181])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    spl5_23),
% 0.20/0.51    inference(avatar_split_clause,[],[f48,f173])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.51  fof(f171,plain,(
% 0.20/0.51    spl5_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f47,f169])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.51  fof(f146,plain,(
% 0.20/0.51    ~spl5_17 | spl5_6 | ~spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f138,f131,f97,f144])).
% 0.20/0.51  fof(f97,plain,(
% 0.20/0.51    spl5_6 <=> r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl5_14 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.20/0.51  fof(f138,plain,(
% 0.20/0.51    ~m1_subset_1(k2_relset_1(sK1,sK2,sK3),k1_zfmisc_1(sK0)) | (spl5_6 | ~spl5_14)),
% 0.20/0.51    inference(resolution,[],[f132,f98])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0) | spl5_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f97])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) ) | ~spl5_14),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    spl5_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f37,f135])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    spl5_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f43,f131])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.51  fof(f119,plain,(
% 0.20/0.51    spl5_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f39,f117])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.51  fof(f115,plain,(
% 0.20/0.51    spl5_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f62,f113])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    spl5_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f61,f109])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    spl5_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f38,f105])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f103,plain,(
% 0.20/0.51    spl5_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f30,f101])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X4] : (~m1_subset_1(X4,sK1) | r2_hidden(k3_funct_2(sK1,sK2,sK3,X4),sK0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (? [X3] : (~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ? [X0,X1] : (? [X2] : (? [X3] : ((~r1_tarski(k2_relset_1(X1,X2,X3),X0) & ! [X4] : (r2_hidden(k3_funct_2(X1,X2,X3,X4),X0) | ~m1_subset_1(X4,X1))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1))),
% 0.20/0.51    inference(ennf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.51    inference(negated_conjecture,[],[f13])).
% 0.20/0.51  fof(f13,conjecture,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (m1_subset_1(X4,X1) => r2_hidden(k3_funct_2(X1,X2,X3,X4),X0)) => r1_tarski(k2_relset_1(X1,X2,X3),X0)))))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t191_funct_2)).
% 0.20/0.51  fof(f99,plain,(
% 0.20/0.51    ~spl5_6),
% 0.20/0.51    inference(avatar_split_clause,[],[f34,f97])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ~r1_tarski(k2_relset_1(sK1,sK2,sK3),sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f95,plain,(
% 0.20/0.51    spl5_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f33,f93])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    spl5_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f32,f89])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    v1_funct_2(sK3,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f87,plain,(
% 0.20/0.51    ~spl5_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f36,f85])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ~v1_xboole_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f31,f77])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v1_funct_1(sK3)),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (23923)------------------------------
% 0.20/0.51  % (23923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (23923)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (23923)Memory used [KB]: 11001
% 0.20/0.51  % (23923)Time elapsed: 0.103 s
% 0.20/0.51  % (23923)------------------------------
% 0.20/0.51  % (23923)------------------------------
% 0.20/0.51  % (23913)Success in time 0.155 s
%------------------------------------------------------------------------------
