%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:54 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  313 ( 549 expanded)
%              Number of leaves         :   79 ( 256 expanded)
%              Depth                    :    9
%              Number of atoms          :  951 (1663 expanded)
%              Number of equality atoms :  178 ( 388 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f706,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f114,f121,f125,f129,f133,f137,f145,f149,f153,f157,f161,f166,f170,f182,f190,f194,f202,f206,f218,f222,f238,f242,f250,f257,f267,f271,f275,f283,f287,f296,f304,f318,f327,f331,f335,f341,f370,f380,f384,f393,f402,f412,f452,f467,f477,f491,f504,f515,f519,f523,f631,f672,f673,f705])).

fof(f705,plain,
    ( spl4_83
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_16
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f678,f325,f316,f155,f135,f119,f619])).

fof(f619,plain,
    ( spl4_83
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).

fof(f119,plain,
    ( spl4_7
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f135,plain,
    ( spl4_11
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f155,plain,
    ( spl4_16
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f316,plain,
    ( spl4_48
  <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f325,plain,
    ( spl4_49
  <=> sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f678,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_16
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f677,f317])).

fof(f317,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f316])).

fof(f677,plain,
    ( sK2 = k9_relat_1(k1_xboole_0,sK2)
    | ~ spl4_7
    | ~ spl4_11
    | ~ spl4_16
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f676,f136])).

fof(f136,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f676,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2)
    | ~ spl4_7
    | ~ spl4_16
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f675,f156])).

fof(f156,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f675,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2)
    | ~ spl4_7
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f326,f463])).

fof(f463,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f326,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f325])).

fof(f673,plain,
    ( ~ spl4_82
    | ~ spl4_6
    | ~ spl4_7
    | spl4_35
    | ~ spl4_83 ),
    inference(avatar_split_clause,[],[f670,f619,f248,f119,f116,f614])).

fof(f614,plain,
    ( spl4_82
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f116,plain,
    ( spl4_6
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f248,plain,
    ( spl4_35
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f670,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_6
    | ~ spl4_7
    | spl4_35
    | ~ spl4_83 ),
    inference(forward_demodulation,[],[f669,f117])).

fof(f117,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f116])).

fof(f669,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl4_7
    | spl4_35
    | ~ spl4_83 ),
    inference(forward_demodulation,[],[f668,f620])).

fof(f620,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_83 ),
    inference(avatar_component_clause,[],[f619])).

fof(f668,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl4_7
    | spl4_35 ),
    inference(forward_demodulation,[],[f249,f463])).

fof(f249,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl4_35 ),
    inference(avatar_component_clause,[],[f248])).

fof(f672,plain,
    ( ~ spl4_84
    | ~ spl4_16
    | ~ spl4_56
    | ~ spl4_57
    | spl4_82 ),
    inference(avatar_split_clause,[],[f633,f614,f368,f359,f155,f623])).

fof(f623,plain,
    ( spl4_84
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f359,plain,
    ( spl4_56
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f368,plain,
    ( spl4_57
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f633,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_16
    | ~ spl4_56
    | ~ spl4_57
    | spl4_82 ),
    inference(subsumption_resolution,[],[f632,f596])).

fof(f596,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f359])).

fof(f632,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl4_16
    | ~ spl4_57
    | spl4_82 ),
    inference(forward_demodulation,[],[f617,f156])).

fof(f617,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl4_57
    | spl4_82 ),
    inference(superposition,[],[f615,f369])).

fof(f369,plain,
    ( ! [X2,X0,X3,X1] :
        ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f368])).

fof(f615,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl4_82 ),
    inference(avatar_component_clause,[],[f614])).

fof(f631,plain,
    ( ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_77
    | spl4_84 ),
    inference(avatar_contradiction_clause,[],[f630])).

fof(f630,plain,
    ( $false
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_30
    | ~ spl4_77
    | spl4_84 ),
    inference(subsumption_resolution,[],[f629,f221])).

fof(f221,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_30
  <=> ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f629,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_27
    | ~ spl4_77
    | spl4_84 ),
    inference(forward_demodulation,[],[f628,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_27
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f628,plain,
    ( ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_18
    | ~ spl4_23
    | ~ spl4_77
    | spl4_84 ),
    inference(subsumption_resolution,[],[f627,f165])).

fof(f165,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl4_18
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f627,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_23
    | ~ spl4_77
    | spl4_84 ),
    inference(subsumption_resolution,[],[f626,f189])).

fof(f189,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl4_23
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f626,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl4_77
    | spl4_84 ),
    inference(superposition,[],[f624,f518])).

fof(f518,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl4_77 ),
    inference(avatar_component_clause,[],[f517])).

fof(f517,plain,
    ( spl4_77
  <=> ! [X1,X0] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f624,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0)
    | spl4_84 ),
    inference(avatar_component_clause,[],[f623])).

fof(f523,plain,
    ( ~ spl4_63
    | spl4_72
    | ~ spl4_76
    | ~ spl4_77 ),
    inference(avatar_split_clause,[],[f522,f517,f513,f489,f397])).

fof(f397,plain,
    ( spl4_63
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f489,plain,
    ( spl4_72
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f513,plain,
    ( spl4_76
  <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f522,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_72
    | ~ spl4_76
    | ~ spl4_77 ),
    inference(subsumption_resolution,[],[f521,f514])).

fof(f514,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f513])).

fof(f521,plain,
    ( ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | spl4_72
    | ~ spl4_77 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | spl4_72
    | ~ spl4_77 ),
    inference(superposition,[],[f490,f518])).

fof(f490,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2)
    | spl4_72 ),
    inference(avatar_component_clause,[],[f489])).

fof(f519,plain,
    ( spl4_77
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f366,f339,f329,f147,f127,f517])).

fof(f127,plain,
    ( spl4_9
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f147,plain,
    ( spl4_14
  <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f329,plain,
    ( spl4_50
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f339,plain,
    ( spl4_52
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_relat_1(X1)
        | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f365,f148])).

fof(f148,plain,
    ( ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f365,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl4_9
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f364,f128])).

fof(f128,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f364,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1) )
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(duplicate_literal_removal,[],[f362])).

fof(f362,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1)))
        | ~ v1_relat_1(k6_relat_1(X1))
        | ~ v1_relat_1(X0)
        | ~ r1_tarski(k2_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(superposition,[],[f340,f330])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( k5_relat_1(X1,k6_relat_1(X0)) = X1
        | ~ r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f329])).

fof(f340,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f339])).

fof(f515,plain,
    ( ~ spl4_63
    | spl4_76
    | ~ spl4_69
    | ~ spl4_74 ),
    inference(avatar_split_clause,[],[f509,f502,f475,f513,f397])).

fof(f475,plain,
    ( spl4_69
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f502,plain,
    ( spl4_74
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r1_tarski(k2_relat_1(X0),X2)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f509,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_69
    | ~ spl4_74 ),
    inference(resolution,[],[f503,f476])).

fof(f476,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl4_69 ),
    inference(avatar_component_clause,[],[f475])).

fof(f503,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r1_tarski(k2_relat_1(X0),X2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f502])).

fof(f504,plain,
    ( spl4_74
    | ~ spl4_38
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f305,f273,f265,f502])).

fof(f265,plain,
    ( spl4_38
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v5_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f273,plain,
    ( spl4_40
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v5_relat_1(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f305,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | r1_tarski(k2_relat_1(X0),X2)
        | ~ v1_relat_1(X0) )
    | ~ spl4_38
    | ~ spl4_40 ),
    inference(resolution,[],[f274,f266])).

fof(f266,plain,
    ( ! [X0,X1] :
        ( ~ v5_relat_1(X1,X0)
        | r1_tarski(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f265])).

fof(f274,plain,
    ( ! [X2,X0,X1] :
        ( v5_relat_1(X2,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_40 ),
    inference(avatar_component_clause,[],[f273])).

fof(f491,plain,
    ( ~ spl4_72
    | spl4_60
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f473,f465,f382,f489])).

fof(f382,plain,
    ( spl4_60
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f465,plain,
    ( spl4_68
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f473,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2)
    | spl4_60
    | ~ spl4_68 ),
    inference(backward_demodulation,[],[f383,f466])).

fof(f466,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f465])).

fof(f383,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl4_60 ),
    inference(avatar_component_clause,[],[f382])).

fof(f477,plain,
    ( spl4_69
    | ~ spl4_33
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f469,f465,f240,f475])).

fof(f240,plain,
    ( spl4_33
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f469,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ spl4_33
    | ~ spl4_68 ),
    inference(backward_demodulation,[],[f241,f466])).

fof(f241,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f240])).

fof(f467,plain,
    ( spl4_7
    | spl4_68
    | ~ spl4_32
    | ~ spl4_33
    | ~ spl4_64 ),
    inference(avatar_split_clause,[],[f417,f400,f240,f236,f465,f119])).

fof(f236,plain,
    ( spl4_32
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f400,plain,
    ( spl4_64
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relat_1(sK2) = X0
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).

fof(f417,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl4_32
    | ~ spl4_33
    | ~ spl4_64 ),
    inference(subsumption_resolution,[],[f416,f241])).

fof(f416,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl4_32
    | ~ spl4_64 ),
    inference(resolution,[],[f401,f237])).

fof(f237,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f236])).

fof(f401,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1 )
    | ~ spl4_64 ),
    inference(avatar_component_clause,[],[f400])).

fof(f452,plain,
    ( ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_33
    | ~ spl4_48
    | ~ spl4_49
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_33
    | ~ spl4_48
    | ~ spl4_49
    | spl4_56 ),
    inference(subsumption_resolution,[],[f445,f360])).

fof(f360,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f359])).

fof(f445,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_33
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f436,f439])).

fof(f439,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_48
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f438,f317])).

fof(f438,plain,
    ( sK2 = k9_relat_1(k1_xboole_0,sK2)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f437,f136])).

fof(f437,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2)
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f433,f160])).

fof(f160,plain,
    ( ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_17
  <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f433,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))),sK2)
    | ~ spl4_6
    | ~ spl4_49 ),
    inference(backward_demodulation,[],[f326,f117])).

fof(f436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_6
    | ~ spl4_17
    | ~ spl4_33 ),
    inference(forward_demodulation,[],[f430,f160])).

fof(f430,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))))
    | ~ spl4_6
    | ~ spl4_33 ),
    inference(backward_demodulation,[],[f241,f117])).

fof(f412,plain,
    ( ~ spl4_13
    | ~ spl4_29
    | ~ spl4_33
    | spl4_63 ),
    inference(avatar_contradiction_clause,[],[f409])).

fof(f409,plain,
    ( $false
    | ~ spl4_13
    | ~ spl4_29
    | ~ spl4_33
    | spl4_63 ),
    inference(unit_resulting_resolution,[],[f144,f241,f398,f217])).

fof(f217,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_29 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_29
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f398,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_63 ),
    inference(avatar_component_clause,[],[f397])).

fof(f144,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_13
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f402,plain,
    ( ~ spl4_63
    | spl4_64
    | ~ spl4_39
    | ~ spl4_51
    | ~ spl4_62 ),
    inference(avatar_split_clause,[],[f395,f391,f333,f269,f400,f397])).

fof(f269,plain,
    ( spl4_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f333,plain,
    ( spl4_51
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f391,plain,
    ( spl4_62
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f395,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1)
        | k1_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl4_39
    | ~ spl4_51
    | ~ spl4_62 ),
    inference(subsumption_resolution,[],[f394,f270])).

fof(f270,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f269])).

fof(f394,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v4_relat_1(sK2,X0)
        | k1_relat_1(sK2) = X0
        | ~ v1_relat_1(sK2) )
    | ~ spl4_51
    | ~ spl4_62 ),
    inference(resolution,[],[f392,f334])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f333])).

fof(f392,plain,
    ( ! [X0,X1] :
        ( v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | ~ v1_funct_2(sK2,X0,X1) )
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f391])).

fof(f393,plain,
    ( spl4_62
    | ~ spl4_1
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f385,f378,f96,f391])).

fof(f96,plain,
    ( spl4_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f378,plain,
    ( spl4_59
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f385,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(sK2,X0) )
    | ~ spl4_1
    | ~ spl4_59 ),
    inference(resolution,[],[f379,f97])).

fof(f97,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f379,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | v1_partfun1(X2,X0) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f378])).

fof(f384,plain,
    ( ~ spl4_60
    | ~ spl4_33
    | spl4_35
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f376,f368,f248,f240,f382])).

fof(f376,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ spl4_33
    | spl4_35
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f375,f241])).

fof(f375,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl4_35
    | ~ spl4_57 ),
    inference(superposition,[],[f249,f369])).

fof(f380,plain,(
    spl4_59 ),
    inference(avatar_split_clause,[],[f85,f378])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

fof(f370,plain,(
    spl4_57 ),
    inference(avatar_split_clause,[],[f87,f368])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f341,plain,(
    spl4_52 ),
    inference(avatar_split_clause,[],[f63,f339])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

fof(f335,plain,(
    spl4_51 ),
    inference(avatar_split_clause,[],[f77,f333])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f331,plain,(
    spl4_50 ),
    inference(avatar_split_clause,[],[f70,f329])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

fof(f327,plain,
    ( spl4_49
    | ~ spl4_33
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f319,f285,f240,f325])).

fof(f285,plain,
    ( spl4_43
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f319,plain,
    ( sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2)
    | ~ spl4_33
    | ~ spl4_43 ),
    inference(resolution,[],[f286,f241])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k9_relat_1(k6_relat_1(X0),X1) = X1 )
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f285])).

fof(f318,plain,
    ( spl4_48
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f314,f302,f281,f204,f164,f316])).

fof(f281,plain,
    ( spl4_42
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f302,plain,
    ( spl4_46
  <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

% (21669)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f314,plain,
    ( ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f313,f205])).

fof(f313,plain,
    ( ! [X0] : k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
    | ~ spl4_18
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f312,f165])).

fof(f312,plain,
    ( ! [X0] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl4_42
    | ~ spl4_46 ),
    inference(superposition,[],[f282,f303])).

fof(f303,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f302])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f281])).

fof(f304,plain,
    ( spl4_46
    | ~ spl4_5
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f299,f294,f112,f302])).

fof(f112,plain,
    ( spl4_5
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f294,plain,
    ( spl4_45
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f299,plain,
    ( ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
    | ~ spl4_5
    | ~ spl4_45 ),
    inference(resolution,[],[f295,f113])).

fof(f113,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k7_relat_1(X0,X1) )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl4_45
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f263,f255,f180,f294])).

fof(f180,plain,
    ( spl4_22
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f255,plain,
    ( spl4_36
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f263,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl4_22
    | ~ spl4_36 ),
    inference(resolution,[],[f256,f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k7_relat_1(X0,X1))
        | ~ v1_xboole_0(X0) )
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f180])).

fof(f256,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f255])).

fof(f287,plain,(
    spl4_43 ),
    inference(avatar_split_clause,[],[f73,f285])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

% (21668)Termination reason: Refutation not found, incomplete strategy

% (21668)Memory used [KB]: 1918
% (21668)Time elapsed: 0.084 s
% (21668)------------------------------
% (21668)------------------------------
fof(f283,plain,(
    spl4_42 ),
    inference(avatar_split_clause,[],[f69,f281])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f275,plain,(
    spl4_40 ),
    inference(avatar_split_clause,[],[f84,f273])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f271,plain,(
    spl4_39 ),
    inference(avatar_split_clause,[],[f83,f269])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f267,plain,(
    spl4_38 ),
    inference(avatar_split_clause,[],[f72,f265])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f257,plain,
    ( spl4_36
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f252,f200,f112,f255])).

fof(f200,plain,
    ( spl4_26
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

% (21655)Refutation not found, incomplete strategy% (21655)------------------------------
% (21655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f252,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(resolution,[],[f201,f113])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | X0 = X1
        | ~ v1_xboole_0(X1) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f200])).

fof(f250,plain,
    ( ~ spl4_35
    | ~ spl4_2
    | ~ spl4_3
    | spl4_10
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f230,f192,f131,f104,f100,f248])).

fof(f100,plain,
    ( spl4_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f104,plain,
    ( spl4_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f131,plain,
    ( spl4_10
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f192,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f230,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_10
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f225,f224])).

fof(f224,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl4_3
    | ~ spl4_24 ),
    inference(resolution,[],[f193,f105])).

fof(f105,plain,
    ( l1_struct_0(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f193,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f192])).

fof(f225,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl4_2
    | spl4_10
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f132,f223])).

fof(f223,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(resolution,[],[f193,f101])).

fof(f101,plain,
    ( l1_struct_0(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f132,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f242,plain,
    ( spl4_33
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f229,f192,f123,f104,f100,f240])).

fof(f123,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f229,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f226,f224])).

fof(f226,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl4_2
    | ~ spl4_8
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f124,f223])).

fof(f124,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f238,plain,
    ( spl4_32
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f228,f192,f108,f104,f100,f236])).

fof(f108,plain,
    ( spl4_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f228,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f227,f224])).

fof(f227,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(backward_demodulation,[],[f109,f223])).

fof(f109,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f222,plain,
    ( spl4_30
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f210,f204,f168,f159,f220])).

fof(f168,plain,
    ( spl4_19
  <=> ! [X1,X0] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f210,plain,
    ( ! [X1] : r1_tarski(k1_xboole_0,X1)
    | ~ spl4_17
    | ~ spl4_19
    | ~ spl4_27 ),
    inference(forward_demodulation,[],[f208,f205])).

fof(f208,plain,
    ( ! [X1] : r1_tarski(k2_relat_1(k1_xboole_0),X1)
    | ~ spl4_17
    | ~ spl4_19 ),
    inference(superposition,[],[f169,f160])).

fof(f169,plain,
    ( ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f168])).

fof(f218,plain,(
    spl4_29 ),
    inference(avatar_split_clause,[],[f64,f216])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f206,plain,
    ( spl4_27
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f184,f151,f135,f204])).

fof(f151,plain,
    ( spl4_15
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f184,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(superposition,[],[f152,f136])).

fof(f152,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f151])).

fof(f202,plain,(
    spl4_26 ),
    inference(avatar_split_clause,[],[f81,f200])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f194,plain,(
    spl4_24 ),
    inference(avatar_split_clause,[],[f61,f192])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f190,plain,
    ( spl4_23
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f183,f147,f135,f188])).

fof(f183,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl4_11
    | ~ spl4_14 ),
    inference(superposition,[],[f148,f136])).

fof(f182,plain,(
    spl4_22 ),
    inference(avatar_split_clause,[],[f93,f180])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k7_relat_1(X0,X1)) ) ),
    inference(subsumption_resolution,[],[f74,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ v1_relat_1(X0)
      | v1_xboole_0(k7_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) )
      | ~ v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X0)
        & v1_xboole_0(X0) )
     => ( v1_relat_1(k7_relat_1(X0,X1))
        & v1_xboole_0(k7_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

fof(f170,plain,(
    spl4_19 ),
    inference(avatar_split_clause,[],[f68,f168])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).

fof(f166,plain,
    ( spl4_18
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f162,f135,f127,f164])).

fof(f162,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(superposition,[],[f128,f136])).

fof(f161,plain,(
    spl4_17 ),
    inference(avatar_split_clause,[],[f90,f159])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f157,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f89,f155])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f153,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f60,f151])).

fof(f60,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f149,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f59,f147])).

fof(f59,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f145,plain,(
    spl4_13 ),
    inference(avatar_split_clause,[],[f67,f143])).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f137,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f57,f135])).

fof(f57,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f133,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f53,f131])).

fof(f53,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f129,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f58,f127])).

fof(f58,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f125,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f52,f123])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f27])).

fof(f121,plain,
    ( spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f49,f119,f116])).

fof(f49,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f114,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f56,f112])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f51,f108])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f106,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f55,f104])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f27])).

fof(f102,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f54,f100])).

fof(f54,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f98,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f50,f96])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:19:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (21660)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (21663)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (21664)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.48  % (21661)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.48  % (21670)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (21657)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (21656)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (21659)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.49  % (21668)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.49  % (21656)Refutation not found, incomplete strategy% (21656)------------------------------
% 0.20/0.49  % (21656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (21656)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (21656)Memory used [KB]: 10618
% 0.20/0.49  % (21656)Time elapsed: 0.069 s
% 0.20/0.49  % (21656)------------------------------
% 0.20/0.49  % (21656)------------------------------
% 0.20/0.49  % (21655)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (21658)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.50  % (21668)Refutation not found, incomplete strategy% (21668)------------------------------
% 0.20/0.50  % (21668)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21658)Refutation not found, incomplete strategy% (21658)------------------------------
% 0.20/0.50  % (21658)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (21658)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21658)Memory used [KB]: 10746
% 0.20/0.50  % (21658)Time elapsed: 0.082 s
% 0.20/0.50  % (21658)------------------------------
% 0.20/0.50  % (21658)------------------------------
% 0.20/0.50  % (21662)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.50  % (21664)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % (21672)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f706,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f98,f102,f106,f110,f114,f121,f125,f129,f133,f137,f145,f149,f153,f157,f161,f166,f170,f182,f190,f194,f202,f206,f218,f222,f238,f242,f250,f257,f267,f271,f275,f283,f287,f296,f304,f318,f327,f331,f335,f341,f370,f380,f384,f393,f402,f412,f452,f467,f477,f491,f504,f515,f519,f523,f631,f672,f673,f705])).
% 0.20/0.50  fof(f705,plain,(
% 0.20/0.50    spl4_83 | ~spl4_7 | ~spl4_11 | ~spl4_16 | ~spl4_48 | ~spl4_49),
% 0.20/0.50    inference(avatar_split_clause,[],[f678,f325,f316,f155,f135,f119,f619])).
% 0.20/0.50  fof(f619,plain,(
% 0.20/0.50    spl4_83 <=> k1_xboole_0 = sK2),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_83])])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl4_7 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.50  fof(f135,plain,(
% 0.20/0.50    spl4_11 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.50  fof(f155,plain,(
% 0.20/0.50    spl4_16 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.20/0.50  fof(f316,plain,(
% 0.20/0.50    spl4_48 <=> ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.20/0.50  fof(f325,plain,(
% 0.20/0.50    spl4_49 <=> sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.20/0.50  fof(f678,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | (~spl4_7 | ~spl4_11 | ~spl4_16 | ~spl4_48 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f677,f317])).
% 0.20/0.50  fof(f317,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | ~spl4_48),
% 0.20/0.50    inference(avatar_component_clause,[],[f316])).
% 0.20/0.50  fof(f677,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k1_xboole_0,sK2) | (~spl4_7 | ~spl4_11 | ~spl4_16 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f676,f136])).
% 0.20/0.50  fof(f136,plain,(
% 0.20/0.50    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_11),
% 0.20/0.50    inference(avatar_component_clause,[],[f135])).
% 0.20/0.50  fof(f676,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2) | (~spl4_7 | ~spl4_16 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f675,f156])).
% 0.20/0.50  fof(f156,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl4_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f155])).
% 0.20/0.50  fof(f675,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k1_xboole_0)),sK2) | (~spl4_7 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f326,f463])).
% 0.20/0.50  fof(f463,plain,(
% 0.20/0.50    k1_xboole_0 = k2_struct_0(sK1) | ~spl4_7),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f326,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) | ~spl4_49),
% 0.20/0.50    inference(avatar_component_clause,[],[f325])).
% 0.20/0.50  fof(f673,plain,(
% 0.20/0.50    ~spl4_82 | ~spl4_6 | ~spl4_7 | spl4_35 | ~spl4_83),
% 0.20/0.50    inference(avatar_split_clause,[],[f670,f619,f248,f119,f116,f614])).
% 0.20/0.50  fof(f614,plain,(
% 0.20/0.50    spl4_82 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    spl4_6 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.50  fof(f248,plain,(
% 0.20/0.50    spl4_35 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 0.20/0.50  fof(f670,plain,(
% 0.20/0.50    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_6 | ~spl4_7 | spl4_35 | ~spl4_83)),
% 0.20/0.50    inference(forward_demodulation,[],[f669,f117])).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    k1_xboole_0 = k2_struct_0(sK0) | ~spl4_6),
% 0.20/0.50    inference(avatar_component_clause,[],[f116])).
% 0.20/0.50  fof(f669,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl4_7 | spl4_35 | ~spl4_83)),
% 0.20/0.50    inference(forward_demodulation,[],[f668,f620])).
% 0.20/0.50  fof(f620,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | ~spl4_83),
% 0.20/0.50    inference(avatar_component_clause,[],[f619])).
% 0.20/0.50  fof(f668,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) | (~spl4_7 | spl4_35)),
% 0.20/0.50    inference(forward_demodulation,[],[f249,f463])).
% 0.20/0.50  fof(f249,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl4_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f248])).
% 0.20/0.50  fof(f672,plain,(
% 0.20/0.50    ~spl4_84 | ~spl4_16 | ~spl4_56 | ~spl4_57 | spl4_82),
% 0.20/0.50    inference(avatar_split_clause,[],[f633,f614,f368,f359,f155,f623])).
% 0.20/0.50  fof(f623,plain,(
% 0.20/0.50    spl4_84 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    spl4_56 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 0.20/0.50  fof(f368,plain,(
% 0.20/0.50    spl4_57 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.20/0.50  fof(f633,plain,(
% 0.20/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_16 | ~spl4_56 | ~spl4_57 | spl4_82)),
% 0.20/0.50    inference(subsumption_resolution,[],[f632,f596])).
% 0.20/0.50  fof(f596,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f359])).
% 0.20/0.50  fof(f632,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | (~spl4_16 | ~spl4_57 | spl4_82)),
% 0.20/0.50    inference(forward_demodulation,[],[f617,f156])).
% 0.20/0.50  fof(f617,plain,(
% 0.20/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl4_57 | spl4_82)),
% 0.20/0.50    inference(superposition,[],[f615,f369])).
% 0.20/0.50  fof(f369,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_57),
% 0.20/0.50    inference(avatar_component_clause,[],[f368])).
% 0.20/0.50  fof(f615,plain,(
% 0.20/0.50    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl4_82),
% 0.20/0.50    inference(avatar_component_clause,[],[f614])).
% 0.20/0.50  fof(f631,plain,(
% 0.20/0.50    ~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_30 | ~spl4_77 | spl4_84),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f630])).
% 0.20/0.50  fof(f630,plain,(
% 0.20/0.50    $false | (~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_30 | ~spl4_77 | spl4_84)),
% 0.20/0.50    inference(subsumption_resolution,[],[f629,f221])).
% 0.20/0.50  fof(f221,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | ~spl4_30),
% 0.20/0.50    inference(avatar_component_clause,[],[f220])).
% 0.20/0.50  fof(f220,plain,(
% 0.20/0.50    spl4_30 <=> ! [X1] : r1_tarski(k1_xboole_0,X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.50  fof(f629,plain,(
% 0.20/0.50    ~r1_tarski(k1_xboole_0,k1_xboole_0) | (~spl4_18 | ~spl4_23 | ~spl4_27 | ~spl4_77 | spl4_84)),
% 0.20/0.50    inference(forward_demodulation,[],[f628,f205])).
% 0.20/0.50  fof(f205,plain,(
% 0.20/0.50    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl4_27),
% 0.20/0.50    inference(avatar_component_clause,[],[f204])).
% 0.20/0.50  fof(f204,plain,(
% 0.20/0.50    spl4_27 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.50  fof(f628,plain,(
% 0.20/0.50    ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_18 | ~spl4_23 | ~spl4_77 | spl4_84)),
% 0.20/0.50    inference(subsumption_resolution,[],[f627,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    v1_relat_1(k1_xboole_0) | ~spl4_18),
% 0.20/0.50    inference(avatar_component_clause,[],[f164])).
% 0.20/0.50  fof(f164,plain,(
% 0.20/0.50    spl4_18 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.20/0.50  fof(f627,plain,(
% 0.20/0.50    ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_23 | ~spl4_77 | spl4_84)),
% 0.20/0.50    inference(subsumption_resolution,[],[f626,f189])).
% 0.20/0.50  fof(f189,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl4_23),
% 0.20/0.50    inference(avatar_component_clause,[],[f188])).
% 0.20/0.50  fof(f188,plain,(
% 0.20/0.50    spl4_23 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.50  fof(f626,plain,(
% 0.20/0.50    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) | (~spl4_77 | spl4_84)),
% 0.20/0.50    inference(superposition,[],[f624,f518])).
% 0.20/0.50  fof(f518,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | ~spl4_77),
% 0.20/0.50    inference(avatar_component_clause,[],[f517])).
% 0.20/0.50  fof(f517,plain,(
% 0.20/0.50    spl4_77 <=> ! [X1,X0] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 0.20/0.50  fof(f624,plain,(
% 0.20/0.50    k1_xboole_0 != k10_relat_1(k1_xboole_0,k1_xboole_0) | spl4_84),
% 0.20/0.50    inference(avatar_component_clause,[],[f623])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    ~spl4_63 | spl4_72 | ~spl4_76 | ~spl4_77),
% 0.20/0.50    inference(avatar_split_clause,[],[f522,f517,f513,f489,f397])).
% 0.20/0.50  fof(f397,plain,(
% 0.20/0.50    spl4_63 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.20/0.50  fof(f489,plain,(
% 0.20/0.50    spl4_72 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 0.20/0.50  fof(f513,plain,(
% 0.20/0.50    spl4_76 <=> r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 0.20/0.50  fof(f522,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | (spl4_72 | ~spl4_76 | ~spl4_77)),
% 0.20/0.50    inference(subsumption_resolution,[],[f521,f514])).
% 0.20/0.50  fof(f514,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~spl4_76),
% 0.20/0.50    inference(avatar_component_clause,[],[f513])).
% 0.20/0.50  fof(f521,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | (spl4_72 | ~spl4_77)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f520])).
% 0.20/0.50  fof(f520,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | (spl4_72 | ~spl4_77)),
% 0.20/0.50    inference(superposition,[],[f490,f518])).
% 0.20/0.50  fof(f490,plain,(
% 0.20/0.50    k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2) | spl4_72),
% 0.20/0.50    inference(avatar_component_clause,[],[f489])).
% 0.20/0.50  fof(f519,plain,(
% 0.20/0.50    spl4_77 | ~spl4_9 | ~spl4_14 | ~spl4_50 | ~spl4_52),
% 0.20/0.50    inference(avatar_split_clause,[],[f366,f339,f329,f147,f127,f517])).
% 0.20/0.50  fof(f127,plain,(
% 0.20/0.50    spl4_9 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    spl4_14 <=> ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.50  fof(f329,plain,(
% 0.20/0.50    spl4_50 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 0.20/0.50  fof(f339,plain,(
% 0.20/0.50    spl4_52 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 0.20/0.50  fof(f366,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl4_9 | ~spl4_14 | ~spl4_50 | ~spl4_52)),
% 0.20/0.50    inference(forward_demodulation,[],[f365,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_14),
% 0.20/0.50    inference(avatar_component_clause,[],[f147])).
% 0.20/0.50  fof(f365,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl4_9 | ~spl4_50 | ~spl4_52)),
% 0.20/0.50    inference(subsumption_resolution,[],[f364,f128])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl4_9),
% 0.20/0.50    inference(avatar_component_clause,[],[f127])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1)) ) | (~spl4_50 | ~spl4_52)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f362])).
% 0.20/0.50  fof(f362,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(X0) = k10_relat_1(X0,k1_relat_1(k6_relat_1(X1))) | ~v1_relat_1(k6_relat_1(X1)) | ~v1_relat_1(X0) | ~r1_tarski(k2_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl4_50 | ~spl4_52)),
% 0.20/0.50    inference(superposition,[],[f340,f330])).
% 0.20/0.50  fof(f330,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_50),
% 0.20/0.50    inference(avatar_component_clause,[],[f329])).
% 0.20/0.50  fof(f340,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl4_52),
% 0.20/0.50    inference(avatar_component_clause,[],[f339])).
% 0.20/0.50  fof(f515,plain,(
% 0.20/0.50    ~spl4_63 | spl4_76 | ~spl4_69 | ~spl4_74),
% 0.20/0.50    inference(avatar_split_clause,[],[f509,f502,f475,f513,f397])).
% 0.20/0.50  fof(f475,plain,(
% 0.20/0.50    spl4_69 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 0.20/0.50  fof(f502,plain,(
% 0.20/0.50    spl4_74 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 0.20/0.50  fof(f509,plain,(
% 0.20/0.50    r1_tarski(k2_relat_1(sK2),k2_struct_0(sK1)) | ~v1_relat_1(sK2) | (~spl4_69 | ~spl4_74)),
% 0.20/0.50    inference(resolution,[],[f503,f476])).
% 0.20/0.50  fof(f476,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~spl4_69),
% 0.20/0.50    inference(avatar_component_clause,[],[f475])).
% 0.20/0.50  fof(f503,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) ) | ~spl4_74),
% 0.20/0.50    inference(avatar_component_clause,[],[f502])).
% 0.20/0.50  fof(f504,plain,(
% 0.20/0.50    spl4_74 | ~spl4_38 | ~spl4_40),
% 0.20/0.50    inference(avatar_split_clause,[],[f305,f273,f265,f502])).
% 0.20/0.50  fof(f265,plain,(
% 0.20/0.50    spl4_38 <=> ! [X1,X0] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.50  fof(f273,plain,(
% 0.20/0.50    spl4_40 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.20/0.50  fof(f305,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) ) | (~spl4_38 | ~spl4_40)),
% 0.20/0.50    inference(resolution,[],[f274,f266])).
% 0.20/0.50  fof(f266,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl4_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f265])).
% 0.20/0.50  fof(f274,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_40),
% 0.20/0.50    inference(avatar_component_clause,[],[f273])).
% 0.20/0.50  fof(f491,plain,(
% 0.20/0.50    ~spl4_72 | spl4_60 | ~spl4_68),
% 0.20/0.50    inference(avatar_split_clause,[],[f473,f465,f382,f489])).
% 0.20/0.50  fof(f382,plain,(
% 0.20/0.50    spl4_60 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 0.20/0.50  fof(f465,plain,(
% 0.20/0.50    spl4_68 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.20/0.50  fof(f473,plain,(
% 0.20/0.50    k10_relat_1(sK2,k2_struct_0(sK1)) != k1_relat_1(sK2) | (spl4_60 | ~spl4_68)),
% 0.20/0.50    inference(backward_demodulation,[],[f383,f466])).
% 0.20/0.50  fof(f466,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl4_68),
% 0.20/0.50    inference(avatar_component_clause,[],[f465])).
% 0.20/0.50  fof(f383,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl4_60),
% 0.20/0.50    inference(avatar_component_clause,[],[f382])).
% 0.20/0.50  fof(f477,plain,(
% 0.20/0.50    spl4_69 | ~spl4_33 | ~spl4_68),
% 0.20/0.50    inference(avatar_split_clause,[],[f469,f465,f240,f475])).
% 0.20/0.50  fof(f240,plain,(
% 0.20/0.50    spl4_33 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.20/0.50  fof(f469,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | (~spl4_33 | ~spl4_68)),
% 0.20/0.50    inference(backward_demodulation,[],[f241,f466])).
% 0.20/0.50  fof(f241,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl4_33),
% 0.20/0.50    inference(avatar_component_clause,[],[f240])).
% 0.20/0.50  fof(f467,plain,(
% 0.20/0.50    spl4_7 | spl4_68 | ~spl4_32 | ~spl4_33 | ~spl4_64),
% 0.20/0.50    inference(avatar_split_clause,[],[f417,f400,f240,f236,f465,f119])).
% 0.20/0.50  fof(f236,plain,(
% 0.20/0.50    spl4_32 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.20/0.50  fof(f400,plain,(
% 0.20/0.50    spl4_64 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = X0 | ~v1_funct_2(sK2,X0,X1) | k1_xboole_0 = X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_64])])).
% 0.20/0.50  fof(f417,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_struct_0(sK1) | (~spl4_32 | ~spl4_33 | ~spl4_64)),
% 0.20/0.50    inference(subsumption_resolution,[],[f416,f241])).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | k1_xboole_0 = k2_struct_0(sK1) | (~spl4_32 | ~spl4_64)),
% 0.20/0.50    inference(resolution,[],[f401,f237])).
% 0.20/0.50  fof(f237,plain,(
% 0.20/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl4_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f236])).
% 0.20/0.50  fof(f401,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1) ) | ~spl4_64),
% 0.20/0.50    inference(avatar_component_clause,[],[f400])).
% 0.20/0.50  fof(f452,plain,(
% 0.20/0.50    ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_33 | ~spl4_48 | ~spl4_49 | spl4_56),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f451])).
% 0.20/0.50  fof(f451,plain,(
% 0.20/0.50    $false | (~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_33 | ~spl4_48 | ~spl4_49 | spl4_56)),
% 0.20/0.50    inference(subsumption_resolution,[],[f445,f360])).
% 0.20/0.50  fof(f360,plain,(
% 0.20/0.50    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | spl4_56),
% 0.20/0.50    inference(avatar_component_clause,[],[f359])).
% 0.20/0.50  fof(f445,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_33 | ~spl4_48 | ~spl4_49)),
% 0.20/0.50    inference(backward_demodulation,[],[f436,f439])).
% 0.20/0.50  fof(f439,plain,(
% 0.20/0.50    k1_xboole_0 = sK2 | (~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_48 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f438,f317])).
% 0.20/0.50  fof(f438,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k1_xboole_0,sK2) | (~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f437,f136])).
% 0.20/0.50  fof(f437,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k1_xboole_0),sK2) | (~spl4_6 | ~spl4_17 | ~spl4_49)),
% 0.20/0.50    inference(forward_demodulation,[],[f433,f160])).
% 0.20/0.50  fof(f160,plain,(
% 0.20/0.50    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) ) | ~spl4_17),
% 0.20/0.50    inference(avatar_component_clause,[],[f159])).
% 0.20/0.50  fof(f159,plain,(
% 0.20/0.50    spl4_17 <=> ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.50  fof(f433,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1))),sK2) | (~spl4_6 | ~spl4_49)),
% 0.20/0.50    inference(backward_demodulation,[],[f326,f117])).
% 0.20/0.50  fof(f436,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl4_6 | ~spl4_17 | ~spl4_33)),
% 0.20/0.50    inference(forward_demodulation,[],[f430,f160])).
% 0.20/0.50  fof(f430,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK1)))) | (~spl4_6 | ~spl4_33)),
% 0.20/0.50    inference(backward_demodulation,[],[f241,f117])).
% 0.20/0.50  fof(f412,plain,(
% 0.20/0.50    ~spl4_13 | ~spl4_29 | ~spl4_33 | spl4_63),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f409])).
% 0.20/0.50  fof(f409,plain,(
% 0.20/0.50    $false | (~spl4_13 | ~spl4_29 | ~spl4_33 | spl4_63)),
% 0.20/0.50    inference(unit_resulting_resolution,[],[f144,f241,f398,f217])).
% 0.20/0.50  fof(f217,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl4_29),
% 0.20/0.50    inference(avatar_component_clause,[],[f216])).
% 0.20/0.50  fof(f216,plain,(
% 0.20/0.50    spl4_29 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.20/0.50  fof(f398,plain,(
% 0.20/0.50    ~v1_relat_1(sK2) | spl4_63),
% 0.20/0.50    inference(avatar_component_clause,[],[f397])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl4_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f143])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl4_13 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.50  fof(f402,plain,(
% 0.20/0.50    ~spl4_63 | spl4_64 | ~spl4_39 | ~spl4_51 | ~spl4_62),
% 0.20/0.50    inference(avatar_split_clause,[],[f395,f391,f333,f269,f400,f397])).
% 0.20/0.50  fof(f269,plain,(
% 0.20/0.50    spl4_39 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 0.20/0.50  fof(f333,plain,(
% 0.20/0.50    spl4_51 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 0.20/0.50  fof(f391,plain,(
% 0.20/0.50    spl4_62 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(sK2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 0.20/0.50  fof(f395,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1) | k1_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | (~spl4_39 | ~spl4_51 | ~spl4_62)),
% 0.20/0.50    inference(subsumption_resolution,[],[f394,f270])).
% 0.20/0.50  fof(f270,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl4_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f269])).
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1) | ~v4_relat_1(sK2,X0) | k1_relat_1(sK2) = X0 | ~v1_relat_1(sK2)) ) | (~spl4_51 | ~spl4_62)),
% 0.20/0.50    inference(resolution,[],[f392,f334])).
% 0.20/0.50  fof(f334,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl4_51),
% 0.20/0.50    inference(avatar_component_clause,[],[f333])).
% 0.20/0.50  fof(f392,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~v1_funct_2(sK2,X0,X1)) ) | ~spl4_62),
% 0.20/0.50    inference(avatar_component_clause,[],[f391])).
% 0.20/0.50  fof(f393,plain,(
% 0.20/0.50    spl4_62 | ~spl4_1 | ~spl4_59),
% 0.20/0.50    inference(avatar_split_clause,[],[f385,f378,f96,f391])).
% 0.20/0.50  fof(f96,plain,(
% 0.20/0.50    spl4_1 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.50  fof(f378,plain,(
% 0.20/0.50    spl4_59 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.20/0.50  fof(f385,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(sK2,X0)) ) | (~spl4_1 | ~spl4_59)),
% 0.20/0.50    inference(resolution,[],[f379,f97])).
% 0.20/0.50  fof(f97,plain,(
% 0.20/0.50    v1_funct_1(sK2) | ~spl4_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f96])).
% 0.20/0.50  fof(f379,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) ) | ~spl4_59),
% 0.20/0.50    inference(avatar_component_clause,[],[f378])).
% 0.20/0.50  fof(f384,plain,(
% 0.20/0.50    ~spl4_60 | ~spl4_33 | spl4_35 | ~spl4_57),
% 0.20/0.50    inference(avatar_split_clause,[],[f376,f368,f248,f240,f382])).
% 0.20/0.50  fof(f376,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (~spl4_33 | spl4_35 | ~spl4_57)),
% 0.20/0.50    inference(subsumption_resolution,[],[f375,f241])).
% 0.20/0.50  fof(f375,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (spl4_35 | ~spl4_57)),
% 0.20/0.50    inference(superposition,[],[f249,f369])).
% 0.20/0.50  fof(f380,plain,(
% 0.20/0.50    spl4_59),
% 0.20/0.50    inference(avatar_split_clause,[],[f85,f378])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | v1_partfun1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f46])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).
% 0.20/0.50  fof(f370,plain,(
% 0.20/0.50    spl4_57),
% 0.20/0.50    inference(avatar_split_clause,[],[f87,f368])).
% 0.20/0.50  fof(f87,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f48])).
% 0.20/0.50  fof(f48,plain,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f19])).
% 0.20/0.50  fof(f19,axiom,(
% 0.20/0.50    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.20/0.50  fof(f341,plain,(
% 0.20/0.50    spl4_52),
% 0.20/0.50    inference(avatar_split_clause,[],[f63,f339])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).
% 0.20/0.50  fof(f335,plain,(
% 0.20/0.50    spl4_51),
% 0.20/0.50    inference(avatar_split_clause,[],[f77,f333])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f42])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.20/0.50    inference(ennf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,axiom,(
% 0.20/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.20/0.50  fof(f331,plain,(
% 0.20/0.50    spl4_50),
% 0.20/0.50    inference(avatar_split_clause,[],[f70,f329])).
% 0.20/0.50  fof(f70,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(flattening,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f14])).
% 0.20/0.50  fof(f14,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).
% 0.20/0.50  fof(f327,plain,(
% 0.20/0.50    spl4_49 | ~spl4_33 | ~spl4_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f319,f285,f240,f325])).
% 0.20/0.50  fof(f285,plain,(
% 0.20/0.50    spl4_43 <=> ! [X1,X0] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    sK2 = k9_relat_1(k6_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))),sK2) | (~spl4_33 | ~spl4_43)),
% 0.20/0.50    inference(resolution,[],[f286,f241])).
% 0.20/0.50  fof(f286,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) ) | ~spl4_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f285])).
% 0.20/0.50  fof(f318,plain,(
% 0.20/0.50    spl4_48 | ~spl4_18 | ~spl4_27 | ~spl4_42 | ~spl4_46),
% 0.20/0.50    inference(avatar_split_clause,[],[f314,f302,f281,f204,f164,f316])).
% 0.20/0.50  fof(f281,plain,(
% 0.20/0.50    spl4_42 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.20/0.50  fof(f302,plain,(
% 0.20/0.50    spl4_46 <=> ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.20/0.50  % (21669)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_18 | ~spl4_27 | ~spl4_42 | ~spl4_46)),
% 0.20/0.50    inference(forward_demodulation,[],[f313,f205])).
% 0.20/0.50  fof(f313,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0)) ) | (~spl4_18 | ~spl4_42 | ~spl4_46)),
% 0.20/0.50    inference(subsumption_resolution,[],[f312,f165])).
% 0.20/0.50  fof(f312,plain,(
% 0.20/0.50    ( ! [X0] : (k2_relat_1(k1_xboole_0) = k9_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl4_42 | ~spl4_46)),
% 0.20/0.50    inference(superposition,[],[f282,f303])).
% 0.20/0.50  fof(f303,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | ~spl4_46),
% 0.20/0.50    inference(avatar_component_clause,[],[f302])).
% 0.20/0.50  fof(f282,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl4_42),
% 0.20/0.50    inference(avatar_component_clause,[],[f281])).
% 0.20/0.50  fof(f304,plain,(
% 0.20/0.50    spl4_46 | ~spl4_5 | ~spl4_45),
% 0.20/0.50    inference(avatar_split_clause,[],[f299,f294,f112,f302])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    spl4_5 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.50  fof(f294,plain,(
% 0.20/0.50    spl4_45 <=> ! [X1,X0] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_xboole_0(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.20/0.50  fof(f299,plain,(
% 0.20/0.50    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) ) | (~spl4_5 | ~spl4_45)),
% 0.20/0.50    inference(resolution,[],[f295,f113])).
% 0.20/0.50  fof(f113,plain,(
% 0.20/0.50    v1_xboole_0(k1_xboole_0) | ~spl4_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f112])).
% 0.20/0.50  fof(f295,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k7_relat_1(X0,X1)) ) | ~spl4_45),
% 0.20/0.50    inference(avatar_component_clause,[],[f294])).
% 0.20/0.50  fof(f296,plain,(
% 0.20/0.50    spl4_45 | ~spl4_22 | ~spl4_36),
% 0.20/0.50    inference(avatar_split_clause,[],[f263,f255,f180,f294])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    spl4_22 <=> ! [X1,X0] : (~v1_xboole_0(X0) | v1_xboole_0(k7_relat_1(X0,X1)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.20/0.50  fof(f255,plain,(
% 0.20/0.50    spl4_36 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 0.20/0.50  fof(f263,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl4_22 | ~spl4_36)),
% 0.20/0.50    inference(resolution,[],[f256,f181])).
% 0.20/0.50  fof(f181,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_xboole_0(k7_relat_1(X0,X1)) | ~v1_xboole_0(X0)) ) | ~spl4_22),
% 0.20/0.50    inference(avatar_component_clause,[],[f180])).
% 0.20/0.50  fof(f256,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_36),
% 0.20/0.50    inference(avatar_component_clause,[],[f255])).
% 0.20/0.50  fof(f287,plain,(
% 0.20/0.50    spl4_43),
% 0.20/0.50    inference(avatar_split_clause,[],[f73,f285])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k9_relat_1(k6_relat_1(X0),X1) = X1) )),
% 0.20/0.50    inference(cnf_transformation,[],[f38])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,axiom,(
% 0.20/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.20/0.50  % (21668)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (21668)Memory used [KB]: 1918
% 0.20/0.50  % (21668)Time elapsed: 0.084 s
% 0.20/0.50  % (21668)------------------------------
% 0.20/0.50  % (21668)------------------------------
% 0.20/0.50  fof(f283,plain,(
% 0.20/0.50    spl4_42),
% 0.20/0.50    inference(avatar_split_clause,[],[f69,f281])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f34])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.50  fof(f275,plain,(
% 0.20/0.50    spl4_40),
% 0.20/0.50    inference(avatar_split_clause,[],[f84,f273])).
% 0.20/0.50  fof(f84,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.20/0.50  fof(f271,plain,(
% 0.20/0.50    spl4_39),
% 0.20/0.50    inference(avatar_split_clause,[],[f83,f269])).
% 0.20/0.50  fof(f83,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f45])).
% 0.20/0.50  fof(f267,plain,(
% 0.20/0.50    spl4_38),
% 0.20/0.50    inference(avatar_split_clause,[],[f72,f265])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f37])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 0.20/0.50  fof(f257,plain,(
% 0.20/0.50    spl4_36 | ~spl4_5 | ~spl4_26),
% 0.20/0.50    inference(avatar_split_clause,[],[f252,f200,f112,f255])).
% 0.20/0.51  fof(f200,plain,(
% 0.20/0.51    spl4_26 <=> ! [X1,X0] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.51  % (21655)Refutation not found, incomplete strategy% (21655)------------------------------
% 0.20/0.51  % (21655)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl4_5 | ~spl4_26)),
% 0.20/0.51    inference(resolution,[],[f201,f113])).
% 0.20/0.51  fof(f201,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) ) | ~spl4_26),
% 0.20/0.51    inference(avatar_component_clause,[],[f200])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    ~spl4_35 | ~spl4_2 | ~spl4_3 | spl4_10 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f230,f192,f131,f104,f100,f248])).
% 0.20/0.51  fof(f100,plain,(
% 0.20/0.51    spl4_2 <=> l1_struct_0(sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f104,plain,(
% 0.20/0.51    spl4_3 <=> l1_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    spl4_10 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f192,plain,(
% 0.20/0.51    spl4_24 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.20/0.51  fof(f230,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl4_2 | ~spl4_3 | spl4_10 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f225,f224])).
% 0.20/0.51  fof(f224,plain,(
% 0.20/0.51    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl4_3 | ~spl4_24)),
% 0.20/0.51    inference(resolution,[],[f193,f105])).
% 0.20/0.51  fof(f105,plain,(
% 0.20/0.51    l1_struct_0(sK0) | ~spl4_3),
% 0.20/0.51    inference(avatar_component_clause,[],[f104])).
% 0.20/0.51  fof(f193,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl4_24),
% 0.20/0.51    inference(avatar_component_clause,[],[f192])).
% 0.20/0.51  fof(f225,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl4_2 | spl4_10 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f132,f223])).
% 0.20/0.51  fof(f223,plain,(
% 0.20/0.51    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl4_2 | ~spl4_24)),
% 0.20/0.51    inference(resolution,[],[f193,f101])).
% 0.20/0.51  fof(f101,plain,(
% 0.20/0.51    l1_struct_0(sK1) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f100])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f131])).
% 0.20/0.51  fof(f242,plain,(
% 0.20/0.51    spl4_33 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f229,f192,f123,f104,f100,f240])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.51  fof(f229,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f226,f224])).
% 0.20/0.51  fof(f226,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl4_2 | ~spl4_8 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f124,f223])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl4_8),
% 0.20/0.51    inference(avatar_component_clause,[],[f123])).
% 0.20/0.51  fof(f238,plain,(
% 0.20/0.51    spl4_32 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f228,f192,f108,f104,f100,f236])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    spl4_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f228,plain,(
% 0.20/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f227,f224])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl4_2 | ~spl4_4 | ~spl4_24)),
% 0.20/0.51    inference(backward_demodulation,[],[f109,f223])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f108])).
% 0.20/0.51  fof(f222,plain,(
% 0.20/0.51    spl4_30 | ~spl4_17 | ~spl4_19 | ~spl4_27),
% 0.20/0.51    inference(avatar_split_clause,[],[f210,f204,f168,f159,f220])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    spl4_19 <=> ! [X1,X0] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.20/0.51  fof(f210,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) ) | (~spl4_17 | ~spl4_19 | ~spl4_27)),
% 0.20/0.51    inference(forward_demodulation,[],[f208,f205])).
% 0.20/0.51  fof(f208,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(k2_relat_1(k1_xboole_0),X1)) ) | (~spl4_17 | ~spl4_19)),
% 0.20/0.51    inference(superposition,[],[f169,f160])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) ) | ~spl4_19),
% 0.20/0.51    inference(avatar_component_clause,[],[f168])).
% 0.20/0.51  fof(f218,plain,(
% 0.20/0.51    spl4_29),
% 0.20/0.51    inference(avatar_split_clause,[],[f64,f216])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    spl4_27 | ~spl4_11 | ~spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f184,f151,f135,f204])).
% 0.20/0.51  fof(f151,plain,(
% 0.20/0.51    spl4_15 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f184,plain,(
% 0.20/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_15)),
% 0.20/0.51    inference(superposition,[],[f152,f136])).
% 0.20/0.51  fof(f152,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl4_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f151])).
% 0.20/0.51  fof(f202,plain,(
% 0.20/0.51    spl4_26),
% 0.20/0.51    inference(avatar_split_clause,[],[f81,f200])).
% 0.20/0.51  fof(f81,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f43])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.51  fof(f194,plain,(
% 0.20/0.51    spl4_24),
% 0.20/0.51    inference(avatar_split_clause,[],[f61,f192])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,axiom,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.51  fof(f190,plain,(
% 0.20/0.51    spl4_23 | ~spl4_11 | ~spl4_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f183,f147,f135,f188])).
% 0.20/0.51  fof(f183,plain,(
% 0.20/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl4_11 | ~spl4_14)),
% 0.20/0.51    inference(superposition,[],[f148,f136])).
% 0.20/0.51  fof(f182,plain,(
% 0.20/0.51    spl4_22),
% 0.20/0.51    inference(avatar_split_clause,[],[f93,f180])).
% 0.20/0.51  fof(f93,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k7_relat_1(X0,X1))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f74,f62])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.20/0.51  fof(f74,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~v1_relat_1(X0) | v1_xboole_0(k7_relat_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | ~v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))) | (~v1_relat_1(X0) | ~v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((v1_relat_1(X0) & v1_xboole_0(X0)) => (v1_relat_1(k7_relat_1(X0,X1)) & v1_xboole_0(k7_relat_1(X0,X1))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).
% 0.20/0.51  fof(f170,plain,(
% 0.20/0.51    spl4_19),
% 0.20/0.51    inference(avatar_split_clause,[],[f68,f168])).
% 0.20/0.51  fof(f68,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k2_relat_1(k2_zfmisc_1(X0,X1)),X1)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t194_relat_1)).
% 0.20/0.51  fof(f166,plain,(
% 0.20/0.51    spl4_18 | ~spl4_9 | ~spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f162,f135,f127,f164])).
% 0.20/0.51  fof(f162,plain,(
% 0.20/0.51    v1_relat_1(k1_xboole_0) | (~spl4_9 | ~spl4_11)),
% 0.20/0.51    inference(superposition,[],[f128,f136])).
% 0.20/0.51  fof(f161,plain,(
% 0.20/0.51    spl4_17),
% 0.20/0.51    inference(avatar_split_clause,[],[f90,f159])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f79])).
% 0.20/0.51  fof(f79,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    spl4_16),
% 0.20/0.51    inference(avatar_split_clause,[],[f89,f155])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f80])).
% 0.20/0.51  fof(f80,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f153,plain,(
% 0.20/0.51    spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f60,f151])).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.51  fof(f149,plain,(
% 0.20/0.51    spl4_14),
% 0.20/0.51    inference(avatar_split_clause,[],[f59,f147])).
% 0.20/0.51  fof(f59,plain,(
% 0.20/0.51    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f145,plain,(
% 0.20/0.51    spl4_13),
% 0.20/0.51    inference(avatar_split_clause,[],[f67,f143])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.51  fof(f137,plain,(
% 0.20/0.51    spl4_11),
% 0.20/0.51    inference(avatar_split_clause,[],[f57,f135])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.20/0.51  fof(f133,plain,(
% 0.20/0.51    ~spl4_10),
% 0.20/0.51    inference(avatar_split_clause,[],[f53,f131])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f25])).
% 0.20/0.51  fof(f25,negated_conjecture,(
% 0.20/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f24])).
% 0.20/0.51  fof(f24,conjecture,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    spl4_9),
% 0.20/0.51    inference(avatar_split_clause,[],[f58,f127])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    spl4_8),
% 0.20/0.51    inference(avatar_split_clause,[],[f52,f123])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f121,plain,(
% 0.20/0.51    spl4_6 | ~spl4_7),
% 0.20/0.51    inference(avatar_split_clause,[],[f49,f119,f116])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    spl4_5),
% 0.20/0.51    inference(avatar_split_clause,[],[f56,f112])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    v1_xboole_0(k1_xboole_0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    spl4_4),
% 0.20/0.51    inference(avatar_split_clause,[],[f51,f108])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl4_3),
% 0.20/0.51    inference(avatar_split_clause,[],[f55,f104])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f102,plain,(
% 0.20/0.51    spl4_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f54,f100])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    l1_struct_0(sK1)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  fof(f98,plain,(
% 0.20/0.51    spl4_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f50,f96])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    v1_funct_1(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f27])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (21664)------------------------------
% 0.20/0.51  % (21664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (21664)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (21664)Memory used [KB]: 11001
% 0.20/0.51  % (21664)Time elapsed: 0.029 s
% 0.20/0.51  % (21664)------------------------------
% 0.20/0.51  % (21664)------------------------------
% 0.20/0.51  % (21655)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (21655)Memory used [KB]: 6396
% 0.20/0.51  % (21655)Time elapsed: 0.086 s
% 0.20/0.51  % (21655)------------------------------
% 0.20/0.51  % (21655)------------------------------
% 0.20/0.51  % (21654)Success in time 0.146 s
%------------------------------------------------------------------------------
