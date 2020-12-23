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
% DateTime   : Thu Dec  3 13:02:15 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 369 expanded)
%              Number of leaves         :   43 ( 165 expanded)
%              Depth                    :   10
%              Number of atoms          :  674 (1274 expanded)
%              Number of equality atoms :  125 ( 265 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f593,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f123,f141,f175,f179,f195,f202,f206,f210,f219,f223,f242,f250,f254,f258,f262,f268,f284,f292,f305,f324,f332,f408,f412,f475,f479,f497,f499,f501,f554,f579])).

fof(f579,plain,
    ( ~ spl6_10
    | spl6_13
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl6_10
    | spl6_13
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61 ),
    inference(subsumption_resolution,[],[f577,f122])).

fof(f122,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_10
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f577,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_13
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f576,f535])).

fof(f535,plain,
    ( k1_xboole_0 = k2_funct_1(k1_xboole_0)
    | ~ spl6_49
    | ~ spl6_61 ),
    inference(backward_demodulation,[],[f447,f320])).

fof(f320,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_49
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f447,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f446])).

fof(f446,plain,
    ( spl6_61
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f576,plain,
    ( ~ m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_13
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f575,f320])).

fof(f575,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl6_13
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f134,f407])).

fof(f407,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f322])).

fof(f322,plain,
    ( spl6_50
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f134,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl6_13
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f554,plain,
    ( ~ spl6_10
    | spl6_14
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(avatar_contradiction_clause,[],[f553])).

fof(f553,plain,
    ( $false
    | ~ spl6_10
    | spl6_14
    | ~ spl6_48
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f552,f530])).

fof(f530,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl6_10
    | ~ spl6_48
    | ~ spl6_50
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(trivial_inequality_removal,[],[f529])).

fof(f529,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl6_10
    | ~ spl6_48
    | ~ spl6_50
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f520,f407])).

fof(f520,plain,
    ( ! [X0] :
        ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
        | k1_xboole_0 != sK1 )
    | ~ spl6_10
    | ~ spl6_48
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(forward_demodulation,[],[f519,f447])).

fof(f519,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK1
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl6_10
    | ~ spl6_48
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(subsumption_resolution,[],[f511,f122])).

fof(f511,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | k1_xboole_0 != sK1
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl6_48
    | ~ spl6_61
    | ~ spl6_64 ),
    inference(backward_demodulation,[],[f480,f447])).

fof(f480,plain,
    ( ! [X0] :
        ( k1_xboole_0 != sK1
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0) )
    | ~ spl6_48
    | ~ spl6_64 ),
    inference(superposition,[],[f478,f304])).

fof(f304,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl6_48
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f478,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f477])).

fof(f477,plain,
    ( spl6_64
  <=> ! [X1,X0] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f552,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,sK0)
    | spl6_14
    | ~ spl6_49
    | ~ spl6_50
    | ~ spl6_61 ),
    inference(forward_demodulation,[],[f551,f535])).

fof(f551,plain,
    ( ~ v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0)
    | spl6_14
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f550,f320])).

fof(f550,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0)
    | spl6_14
    | ~ spl6_50 ),
    inference(forward_demodulation,[],[f137,f407])).

fof(f137,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl6_14
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f501,plain,
    ( ~ spl6_62
    | ~ spl6_15
    | spl6_13
    | ~ spl6_37
    | ~ spl6_48
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f484,f410,f303,f240,f133,f139,f449])).

fof(f449,plain,
    ( spl6_62
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f139,plain,
    ( spl6_15
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f240,plain,
    ( spl6_37
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f410,plain,
    ( spl6_57
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f484,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_37
    | ~ spl6_48
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f423,f304])).

fof(f423,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_37
    | ~ spl6_57 ),
    inference(superposition,[],[f241,f411])).

fof(f411,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_57 ),
    inference(avatar_component_clause,[],[f410])).

fof(f241,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f240])).

fof(f499,plain,
    ( spl6_61
    | ~ spl6_62
    | ~ spl6_50
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_30
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f277,f266,f260,f204,f101,f97,f322,f449,f446])).

fof(f97,plain,
    ( spl6_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f101,plain,
    ( spl6_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f204,plain,
    ( spl6_30
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k1_relat_1(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f260,plain,
    ( spl6_42
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f266,plain,
    ( spl6_43
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f277,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_30
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f273,f276])).

fof(f276,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f274,f98])).

fof(f98,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f274,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(superposition,[],[f261,f102])).

fof(f102,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f261,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f260])).

fof(f273,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl6_30
    | ~ spl6_43 ),
    inference(superposition,[],[f205,f267])).

fof(f267,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f266])).

fof(f205,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f497,plain,
    ( ~ spl6_62
    | ~ spl6_15
    | spl6_14
    | ~ spl6_33
    | ~ spl6_48
    | ~ spl6_57 ),
    inference(avatar_split_clause,[],[f483,f410,f303,f221,f136,f139,f449])).

fof(f221,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f483,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_33
    | ~ spl6_48
    | ~ spl6_57 ),
    inference(forward_demodulation,[],[f424,f304])).

fof(f424,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl6_33
    | ~ spl6_57 ),
    inference(superposition,[],[f222,f411])).

fof(f222,plain,
    ( ! [X0] :
        ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f221])).

fof(f479,plain,
    ( spl6_64
    | ~ spl6_41
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f310,f290,f256,f477])).

fof(f256,plain,
    ( spl6_41
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f290,plain,
    ( spl6_46
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f310,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0) )
    | ~ spl6_41
    | ~ spl6_46 ),
    inference(duplicate_literal_removal,[],[f309])).

fof(f309,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
        | v1_funct_2(X1,k1_xboole_0,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) )
    | ~ spl6_41
    | ~ spl6_46 ),
    inference(superposition,[],[f291,f257])).

fof(f257,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f256])).

fof(f291,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f290])).

fof(f475,plain,
    ( ~ spl6_29
    | ~ spl6_1
    | ~ spl6_23
    | spl6_62 ),
    inference(avatar_split_clause,[],[f465,f449,f173,f85,f200])).

fof(f200,plain,
    ( spl6_29
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f85,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f173,plain,
    ( spl6_23
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f465,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_23
    | spl6_62 ),
    inference(subsumption_resolution,[],[f463,f86])).

fof(f86,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f463,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl6_23
    | spl6_62 ),
    inference(resolution,[],[f450,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f450,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl6_62 ),
    inference(avatar_component_clause,[],[f449])).

fof(f412,plain,
    ( ~ spl6_29
    | spl6_57
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f400,f347,f256,f252,f97,f89,f85,f410,f200])).

fof(f89,plain,
    ( spl6_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f252,plain,
    ( spl6_40
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f347,plain,
    ( spl6_54
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f400,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_40
    | ~ spl6_41
    | ~ spl6_54 ),
    inference(backward_demodulation,[],[f270,f399])).

fof(f399,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl6_4
    | ~ spl6_41
    | ~ spl6_54 ),
    inference(subsumption_resolution,[],[f395,f98])).

fof(f395,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_41
    | ~ spl6_54 ),
    inference(superposition,[],[f348,f257])).

fof(f348,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f347])).

fof(f270,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(subsumption_resolution,[],[f269,f86])).

fof(f269,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_40 ),
    inference(resolution,[],[f253,f90])).

fof(f90,plain,
    ( v2_funct_1(sK2)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f253,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) )
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f252])).

fof(f408,plain,
    ( spl6_54
    | spl6_50
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f350,f330,f97,f93,f322,f347])).

fof(f93,plain,
    ( spl6_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f330,plain,
    ( spl6_52
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f350,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_52 ),
    inference(subsumption_resolution,[],[f341,f98])).

fof(f341,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_3
    | ~ spl6_52 ),
    inference(resolution,[],[f331,f94])).

fof(f94,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f331,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f330])).

fof(f332,plain,(
    spl6_52 ),
    inference(avatar_split_clause,[],[f76,f330])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f324,plain,
    ( spl6_49
    | ~ spl6_29
    | ~ spl6_50
    | ~ spl6_31
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f295,f282,f208,f322,f200,f319])).

fof(f208,plain,
    ( spl6_31
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f282,plain,
    ( spl6_44
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f295,plain,
    ( k1_xboole_0 != sK1
    | ~ v1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl6_31
    | ~ spl6_44 ),
    inference(superposition,[],[f209,f283])).

fof(f283,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f282])).

fof(f209,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0)
        | k1_xboole_0 = X0 )
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f305,plain,
    ( spl6_48
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f280,f266,f260,f101,f97,f303])).

fof(f280,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_42
    | ~ spl6_43 ),
    inference(backward_demodulation,[],[f267,f276])).

fof(f292,plain,(
    spl6_46 ),
    inference(avatar_split_clause,[],[f79,f290])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f284,plain,
    ( spl6_44
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f276,f260,f101,f97,f282])).

fof(f268,plain,
    ( spl6_43
    | ~ spl6_29
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f264,f248,f89,f85,f200,f266])).

fof(f248,plain,
    ( spl6_39
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f264,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_39 ),
    inference(subsumption_resolution,[],[f263,f86])).

fof(f263,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl6_2
    | ~ spl6_39 ),
    inference(resolution,[],[f249,f90])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f248])).

fof(f262,plain,(
    spl6_42 ),
    inference(avatar_split_clause,[],[f70,f260])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f258,plain,(
    spl6_41 ),
    inference(avatar_split_clause,[],[f69,f256])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f254,plain,(
    spl6_40 ),
    inference(avatar_split_clause,[],[f57,f252])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f250,plain,(
    spl6_39 ),
    inference(avatar_split_clause,[],[f56,f248])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f242,plain,(
    spl6_37 ),
    inference(avatar_split_clause,[],[f53,f240])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f223,plain,(
    spl6_33 ),
    inference(avatar_split_clause,[],[f52,f221])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f219,plain,
    ( ~ spl6_4
    | ~ spl6_28
    | spl6_29 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_28
    | spl6_29 ),
    inference(unit_resulting_resolution,[],[f201,f98,f194])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl6_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f201,plain,
    ( ~ v1_relat_1(sK2)
    | spl6_29 ),
    inference(avatar_component_clause,[],[f200])).

fof(f210,plain,(
    spl6_31 ),
    inference(avatar_split_clause,[],[f51,f208])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

fof(f206,plain,(
    spl6_30 ),
    inference(avatar_split_clause,[],[f50,f204])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f202,plain,
    ( ~ spl6_29
    | ~ spl6_1
    | spl6_15
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f197,f177,f139,f85,f200])).

fof(f177,plain,
    ( spl6_24
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f197,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl6_1
    | spl6_15
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f196,f86])).

fof(f196,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl6_15
    | ~ spl6_24 ),
    inference(resolution,[],[f178,f140])).

fof(f140,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f178,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f177])).

fof(f195,plain,(
    spl6_28 ),
    inference(avatar_split_clause,[],[f68,f193])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f179,plain,(
    spl6_24 ),
    inference(avatar_split_clause,[],[f55,f177])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f175,plain,(
    spl6_23 ),
    inference(avatar_split_clause,[],[f54,f173])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f141,plain,
    ( ~ spl6_13
    | ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f39,f139,f136,f133])).

fof(f39,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f123,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f47,f121])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f103,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f44,f101])).

fof(f44,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f99,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f42,f97])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f41,f93])).

fof(f41,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f87,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f40,f85])).

fof(f40,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:23:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (30186)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.44  % (30178)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (30190)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.46  % (30183)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (30188)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (30187)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.46  % (30194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (30183)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (30180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (30179)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (30194)Refutation not found, incomplete strategy% (30194)------------------------------
% 0.20/0.48  % (30194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30194)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30194)Memory used [KB]: 10618
% 0.20/0.48  % (30194)Time elapsed: 0.084 s
% 0.20/0.48  % (30194)------------------------------
% 0.20/0.48  % (30194)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f593,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f87,f91,f95,f99,f103,f123,f141,f175,f179,f195,f202,f206,f210,f219,f223,f242,f250,f254,f258,f262,f268,f284,f292,f305,f324,f332,f408,f412,f475,f479,f497,f499,f501,f554,f579])).
% 0.20/0.48  fof(f579,plain,(
% 0.20/0.48    ~spl6_10 | spl6_13 | ~spl6_49 | ~spl6_50 | ~spl6_61),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f578])).
% 0.20/0.48  fof(f578,plain,(
% 0.20/0.48    $false | (~spl6_10 | spl6_13 | ~spl6_49 | ~spl6_50 | ~spl6_61)),
% 0.20/0.48    inference(subsumption_resolution,[],[f577,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl6_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f121])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    spl6_10 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.48  fof(f577,plain,(
% 0.20/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_13 | ~spl6_49 | ~spl6_50 | ~spl6_61)),
% 0.20/0.48    inference(forward_demodulation,[],[f576,f535])).
% 0.20/0.48  fof(f535,plain,(
% 0.20/0.48    k1_xboole_0 = k2_funct_1(k1_xboole_0) | (~spl6_49 | ~spl6_61)),
% 0.20/0.48    inference(backward_demodulation,[],[f447,f320])).
% 0.20/0.48  fof(f320,plain,(
% 0.20/0.48    k1_xboole_0 = sK2 | ~spl6_49),
% 0.20/0.48    inference(avatar_component_clause,[],[f319])).
% 0.20/0.48  fof(f319,plain,(
% 0.20/0.48    spl6_49 <=> k1_xboole_0 = sK2),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.20/0.48  fof(f447,plain,(
% 0.20/0.48    k1_xboole_0 = k2_funct_1(sK2) | ~spl6_61),
% 0.20/0.48    inference(avatar_component_clause,[],[f446])).
% 0.20/0.48  fof(f446,plain,(
% 0.20/0.48    spl6_61 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 0.20/0.48  fof(f576,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_13 | ~spl6_49 | ~spl6_50)),
% 0.20/0.48    inference(forward_demodulation,[],[f575,f320])).
% 0.20/0.48  fof(f575,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl6_13 | ~spl6_50)),
% 0.20/0.48    inference(forward_demodulation,[],[f134,f407])).
% 0.20/0.48  fof(f407,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | ~spl6_50),
% 0.20/0.48    inference(avatar_component_clause,[],[f322])).
% 0.20/0.48  fof(f322,plain,(
% 0.20/0.48    spl6_50 <=> k1_xboole_0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_13),
% 0.20/0.48    inference(avatar_component_clause,[],[f133])).
% 0.20/0.48  fof(f133,plain,(
% 0.20/0.48    spl6_13 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.48  fof(f554,plain,(
% 0.20/0.48    ~spl6_10 | spl6_14 | ~spl6_48 | ~spl6_49 | ~spl6_50 | ~spl6_61 | ~spl6_64),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f553])).
% 0.20/0.48  fof(f553,plain,(
% 0.20/0.48    $false | (~spl6_10 | spl6_14 | ~spl6_48 | ~spl6_49 | ~spl6_50 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(subsumption_resolution,[],[f552,f530])).
% 0.20/0.48  fof(f530,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl6_10 | ~spl6_48 | ~spl6_50 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f529])).
% 0.20/0.48  fof(f529,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl6_10 | ~spl6_48 | ~spl6_50 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(backward_demodulation,[],[f520,f407])).
% 0.20/0.48  fof(f520,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0) | k1_xboole_0 != sK1) ) | (~spl6_10 | ~spl6_48 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(forward_demodulation,[],[f519,f447])).
% 0.20/0.48  fof(f519,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != sK1 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl6_10 | ~spl6_48 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(subsumption_resolution,[],[f511,f122])).
% 0.20/0.48  fof(f511,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | k1_xboole_0 != sK1 | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl6_48 | ~spl6_61 | ~spl6_64)),
% 0.20/0.48    inference(backward_demodulation,[],[f480,f447])).
% 0.20/0.48  fof(f480,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != sK1 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(k2_funct_1(sK2),k1_xboole_0,X0)) ) | (~spl6_48 | ~spl6_64)),
% 0.20/0.48    inference(superposition,[],[f478,f304])).
% 0.20/0.48  fof(f304,plain,(
% 0.20/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl6_48),
% 0.20/0.48    inference(avatar_component_clause,[],[f303])).
% 0.20/0.48  fof(f303,plain,(
% 0.20/0.48    spl6_48 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.20/0.48  fof(f478,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0)) ) | ~spl6_64),
% 0.20/0.48    inference(avatar_component_clause,[],[f477])).
% 0.20/0.48  fof(f477,plain,(
% 0.20/0.48    spl6_64 <=> ! [X1,X0] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.20/0.48  fof(f552,plain,(
% 0.20/0.48    ~v1_funct_2(k1_xboole_0,k1_xboole_0,sK0) | (spl6_14 | ~spl6_49 | ~spl6_50 | ~spl6_61)),
% 0.20/0.48    inference(forward_demodulation,[],[f551,f535])).
% 0.20/0.48  fof(f551,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK0) | (spl6_14 | ~spl6_49 | ~spl6_50)),
% 0.20/0.48    inference(forward_demodulation,[],[f550,f320])).
% 0.20/0.48  fof(f550,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,sK0) | (spl6_14 | ~spl6_50)),
% 0.20/0.48    inference(forward_demodulation,[],[f137,f407])).
% 0.20/0.48  fof(f137,plain,(
% 0.20/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl6_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f136])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    spl6_14 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.48  fof(f501,plain,(
% 0.20/0.48    ~spl6_62 | ~spl6_15 | spl6_13 | ~spl6_37 | ~spl6_48 | ~spl6_57),
% 0.20/0.48    inference(avatar_split_clause,[],[f484,f410,f303,f240,f133,f139,f449])).
% 0.20/0.48  fof(f449,plain,(
% 0.20/0.48    spl6_62 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.20/0.48  fof(f139,plain,(
% 0.20/0.48    spl6_15 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.48  fof(f240,plain,(
% 0.20/0.48    spl6_37 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.20/0.48  fof(f410,plain,(
% 0.20/0.48    spl6_57 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.20/0.48  fof(f484,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_37 | ~spl6_48 | ~spl6_57)),
% 0.20/0.48    inference(forward_demodulation,[],[f423,f304])).
% 0.20/0.48  fof(f423,plain,(
% 0.20/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_37 | ~spl6_57)),
% 0.20/0.48    inference(superposition,[],[f241,f411])).
% 0.20/0.48  fof(f411,plain,(
% 0.20/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl6_57),
% 0.20/0.48    inference(avatar_component_clause,[],[f410])).
% 0.20/0.48  fof(f241,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_37),
% 0.20/0.48    inference(avatar_component_clause,[],[f240])).
% 0.20/0.48  fof(f499,plain,(
% 0.20/0.48    spl6_61 | ~spl6_62 | ~spl6_50 | ~spl6_4 | ~spl6_5 | ~spl6_30 | ~spl6_42 | ~spl6_43),
% 0.20/0.48    inference(avatar_split_clause,[],[f277,f266,f260,f204,f101,f97,f322,f449,f446])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    spl6_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    spl6_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.48  fof(f204,plain,(
% 0.20/0.48    spl6_30 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.20/0.48  fof(f260,plain,(
% 0.20/0.48    spl6_42 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 0.20/0.48  fof(f266,plain,(
% 0.20/0.48    spl6_43 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.20/0.48  fof(f277,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | (~spl6_4 | ~spl6_5 | ~spl6_30 | ~spl6_42 | ~spl6_43)),
% 0.20/0.48    inference(backward_demodulation,[],[f273,f276])).
% 0.20/0.48  fof(f276,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2) | (~spl6_4 | ~spl6_5 | ~spl6_42)),
% 0.20/0.48    inference(subsumption_resolution,[],[f274,f98])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f97])).
% 0.20/0.48  fof(f274,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_5 | ~spl6_42)),
% 0.20/0.48    inference(superposition,[],[f261,f102])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl6_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f101])).
% 0.20/0.48  fof(f261,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_42),
% 0.20/0.48    inference(avatar_component_clause,[],[f260])).
% 0.20/0.48  fof(f273,plain,(
% 0.20/0.48    k1_xboole_0 != k2_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k1_xboole_0 = k2_funct_1(sK2) | (~spl6_30 | ~spl6_43)),
% 0.20/0.48    inference(superposition,[],[f205,f267])).
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl6_43),
% 0.20/0.48    inference(avatar_component_clause,[],[f266])).
% 0.20/0.48  fof(f205,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl6_30),
% 0.20/0.48    inference(avatar_component_clause,[],[f204])).
% 0.20/0.48  fof(f497,plain,(
% 0.20/0.48    ~spl6_62 | ~spl6_15 | spl6_14 | ~spl6_33 | ~spl6_48 | ~spl6_57),
% 0.20/0.48    inference(avatar_split_clause,[],[f483,f410,f303,f221,f136,f139,f449])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    spl6_33 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.48  fof(f483,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_33 | ~spl6_48 | ~spl6_57)),
% 0.20/0.48    inference(forward_demodulation,[],[f424,f304])).
% 0.20/0.48  fof(f424,plain,(
% 0.20/0.48    v1_funct_2(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)),sK0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl6_33 | ~spl6_57)),
% 0.20/0.48    inference(superposition,[],[f222,f411])).
% 0.20/0.48  fof(f222,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_33),
% 0.20/0.48    inference(avatar_component_clause,[],[f221])).
% 0.20/0.48  fof(f479,plain,(
% 0.20/0.48    spl6_64 | ~spl6_41 | ~spl6_46),
% 0.20/0.48    inference(avatar_split_clause,[],[f310,f290,f256,f477])).
% 0.20/0.48  fof(f256,plain,(
% 0.20/0.48    spl6_41 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.20/0.48  fof(f290,plain,(
% 0.20/0.48    spl6_46 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.20/0.48  fof(f310,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0)) ) | (~spl6_41 | ~spl6_46)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f309])).
% 0.20/0.48  fof(f309,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) ) | (~spl6_41 | ~spl6_46)),
% 0.20/0.48    inference(superposition,[],[f291,f257])).
% 0.20/0.48  fof(f257,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_41),
% 0.20/0.48    inference(avatar_component_clause,[],[f256])).
% 0.20/0.48  fof(f291,plain,(
% 0.20/0.48    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl6_46),
% 0.20/0.48    inference(avatar_component_clause,[],[f290])).
% 0.20/0.48  fof(f475,plain,(
% 0.20/0.48    ~spl6_29 | ~spl6_1 | ~spl6_23 | spl6_62),
% 0.20/0.48    inference(avatar_split_clause,[],[f465,f449,f173,f85,f200])).
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    spl6_29 <=> v1_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    spl6_1 <=> v1_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.48  fof(f173,plain,(
% 0.20/0.48    spl6_23 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.48  fof(f465,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | (~spl6_1 | ~spl6_23 | spl6_62)),
% 0.20/0.48    inference(subsumption_resolution,[],[f463,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    v1_funct_1(sK2) | ~spl6_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f85])).
% 0.20/0.48  fof(f463,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl6_23 | spl6_62)),
% 0.20/0.48    inference(resolution,[],[f450,f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_23),
% 0.20/0.48    inference(avatar_component_clause,[],[f173])).
% 0.20/0.48  fof(f450,plain,(
% 0.20/0.48    ~v1_relat_1(k2_funct_1(sK2)) | spl6_62),
% 0.20/0.48    inference(avatar_component_clause,[],[f449])).
% 0.20/0.48  fof(f412,plain,(
% 0.20/0.48    ~spl6_29 | spl6_57 | ~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_40 | ~spl6_41 | ~spl6_54),
% 0.20/0.48    inference(avatar_split_clause,[],[f400,f347,f256,f252,f97,f89,f85,f410,f200])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    spl6_2 <=> v2_funct_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    spl6_40 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.20/0.48  fof(f347,plain,(
% 0.20/0.48    spl6_54 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 0.20/0.48  fof(f400,plain,(
% 0.20/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_40 | ~spl6_41 | ~spl6_54)),
% 0.20/0.48    inference(backward_demodulation,[],[f270,f399])).
% 0.20/0.48  fof(f399,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK2) | (~spl6_4 | ~spl6_41 | ~spl6_54)),
% 0.20/0.48    inference(subsumption_resolution,[],[f395,f98])).
% 0.20/0.48  fof(f395,plain,(
% 0.20/0.48    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_41 | ~spl6_54)),
% 0.20/0.48    inference(superposition,[],[f348,f257])).
% 0.20/0.48  fof(f348,plain,(
% 0.20/0.48    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl6_54),
% 0.20/0.48    inference(avatar_component_clause,[],[f347])).
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_40)),
% 0.20/0.48    inference(subsumption_resolution,[],[f269,f86])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl6_2 | ~spl6_40)),
% 0.20/0.48    inference(resolution,[],[f253,f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    v2_funct_1(sK2) | ~spl6_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f89])).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) ) | ~spl6_40),
% 0.20/0.48    inference(avatar_component_clause,[],[f252])).
% 0.20/0.48  fof(f408,plain,(
% 0.20/0.48    spl6_54 | spl6_50 | ~spl6_3 | ~spl6_4 | ~spl6_52),
% 0.20/0.48    inference(avatar_split_clause,[],[f350,f330,f97,f93,f322,f347])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    spl6_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.48  fof(f330,plain,(
% 0.20/0.48    spl6_52 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.20/0.48  fof(f350,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | (~spl6_3 | ~spl6_4 | ~spl6_52)),
% 0.20/0.48    inference(subsumption_resolution,[],[f341,f98])).
% 0.20/0.48  fof(f341,plain,(
% 0.20/0.48    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl6_3 | ~spl6_52)),
% 0.20/0.48    inference(resolution,[],[f331,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl6_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f93])).
% 0.20/0.48  fof(f331,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_52),
% 0.20/0.48    inference(avatar_component_clause,[],[f330])).
% 0.20/0.48  fof(f332,plain,(
% 0.20/0.48    spl6_52),
% 0.20/0.48    inference(avatar_split_clause,[],[f76,f330])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(flattening,[],[f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.48  fof(f324,plain,(
% 0.20/0.48    spl6_49 | ~spl6_29 | ~spl6_50 | ~spl6_31 | ~spl6_44),
% 0.20/0.48    inference(avatar_split_clause,[],[f295,f282,f208,f322,f200,f319])).
% 0.20/0.48  fof(f208,plain,(
% 0.20/0.48    spl6_31 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.48  fof(f282,plain,(
% 0.20/0.48    spl6_44 <=> sK1 = k2_relat_1(sK2)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 0.20/0.48  fof(f295,plain,(
% 0.20/0.48    k1_xboole_0 != sK1 | ~v1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl6_31 | ~spl6_44)),
% 0.20/0.48    inference(superposition,[],[f209,f283])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    sK1 = k2_relat_1(sK2) | ~spl6_44),
% 0.20/0.48    inference(avatar_component_clause,[],[f282])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0) | k1_xboole_0 = X0) ) | ~spl6_31),
% 0.20/0.48    inference(avatar_component_clause,[],[f208])).
% 0.20/0.48  fof(f305,plain,(
% 0.20/0.48    spl6_48 | ~spl6_4 | ~spl6_5 | ~spl6_42 | ~spl6_43),
% 0.20/0.48    inference(avatar_split_clause,[],[f280,f266,f260,f101,f97,f303])).
% 0.20/0.48  fof(f280,plain,(
% 0.20/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl6_4 | ~spl6_5 | ~spl6_42 | ~spl6_43)),
% 0.20/0.48    inference(backward_demodulation,[],[f267,f276])).
% 0.20/0.48  fof(f292,plain,(
% 0.20/0.48    spl6_46),
% 0.20/0.48    inference(avatar_split_clause,[],[f79,f290])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    spl6_44 | ~spl6_4 | ~spl6_5 | ~spl6_42),
% 0.20/0.48    inference(avatar_split_clause,[],[f276,f260,f101,f97,f282])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    spl6_43 | ~spl6_29 | ~spl6_1 | ~spl6_2 | ~spl6_39),
% 0.20/0.48    inference(avatar_split_clause,[],[f264,f248,f89,f85,f200,f266])).
% 0.20/0.48  fof(f248,plain,(
% 0.20/0.48    spl6_39 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl6_1 | ~spl6_2 | ~spl6_39)),
% 0.20/0.48    inference(subsumption_resolution,[],[f263,f86])).
% 0.20/0.48  fof(f263,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl6_2 | ~spl6_39)),
% 0.20/0.48    inference(resolution,[],[f249,f90])).
% 0.20/0.48  fof(f249,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) ) | ~spl6_39),
% 0.20/0.48    inference(avatar_component_clause,[],[f248])).
% 0.20/0.48  fof(f262,plain,(
% 0.20/0.48    spl6_42),
% 0.20/0.48    inference(avatar_split_clause,[],[f70,f260])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.48  fof(f258,plain,(
% 0.20/0.48    spl6_41),
% 0.20/0.48    inference(avatar_split_clause,[],[f69,f256])).
% 0.20/0.48  fof(f69,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    spl6_40),
% 0.20/0.48    inference(avatar_split_clause,[],[f57,f252])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    spl6_39),
% 0.20/0.48    inference(avatar_split_clause,[],[f56,f248])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    spl6_37),
% 0.20/0.48    inference(avatar_split_clause,[],[f53,f240])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 0.20/0.48  fof(f223,plain,(
% 0.20/0.48    spl6_33),
% 0.20/0.48    inference(avatar_split_clause,[],[f52,f221])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f219,plain,(
% 0.20/0.48    ~spl6_4 | ~spl6_28 | spl6_29),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f217])).
% 0.20/0.48  fof(f217,plain,(
% 0.20/0.48    $false | (~spl6_4 | ~spl6_28 | spl6_29)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f201,f98,f194])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl6_28),
% 0.20/0.48    inference(avatar_component_clause,[],[f193])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    spl6_28 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | spl6_29),
% 0.20/0.48    inference(avatar_component_clause,[],[f200])).
% 0.20/0.48  fof(f210,plain,(
% 0.20/0.48    spl6_31),
% 0.20/0.48    inference(avatar_split_clause,[],[f51,f208])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.48  fof(f206,plain,(
% 0.20/0.48    spl6_30),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f204])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f23])).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    ~spl6_29 | ~spl6_1 | spl6_15 | ~spl6_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f197,f177,f139,f85,f200])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    spl6_24 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ~v1_relat_1(sK2) | (~spl6_1 | spl6_15 | ~spl6_24)),
% 0.20/0.48    inference(subsumption_resolution,[],[f196,f86])).
% 0.20/0.48  fof(f196,plain,(
% 0.20/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl6_15 | ~spl6_24)),
% 0.20/0.48    inference(resolution,[],[f178,f140])).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ~v1_funct_1(k2_funct_1(sK2)) | spl6_15),
% 0.20/0.48    inference(avatar_component_clause,[],[f139])).
% 0.20/0.48  fof(f178,plain,(
% 0.20/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl6_24),
% 0.20/0.48    inference(avatar_component_clause,[],[f177])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    spl6_28),
% 0.20/0.48    inference(avatar_split_clause,[],[f68,f193])).
% 0.20/0.48  fof(f68,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    spl6_24),
% 0.20/0.48    inference(avatar_split_clause,[],[f55,f177])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    spl6_23),
% 0.20/0.48    inference(avatar_split_clause,[],[f54,f173])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ~spl6_13 | ~spl6_14 | ~spl6_15),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f139,f136,f133])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    inference(negated_conjecture,[],[f18])).
% 0.20/0.48  fof(f18,conjecture,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.48  fof(f123,plain,(
% 0.20/0.48    spl6_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f47,f121])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    spl6_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f101])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    spl6_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f97])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    spl6_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f93])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    spl6_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f89])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v2_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl6_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f85])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (30183)------------------------------
% 0.20/0.48  % (30183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30183)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (30183)Memory used [KB]: 10874
% 0.20/0.48  % (30183)Time elapsed: 0.069 s
% 0.20/0.48  % (30183)------------------------------
% 0.20/0.48  % (30183)------------------------------
% 0.20/0.48  % (30177)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (30172)Success in time 0.135 s
%------------------------------------------------------------------------------
