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
% DateTime   : Thu Dec  3 13:09:33 EST 2020

% Result     : Theorem 5.80s
% Output     : Refutation 6.25s
% Verified   : 
% Statistics : Number of formulae       :  733 (2299 expanded)
%              Number of leaves         :   96 ( 881 expanded)
%              Depth                    :   30
%              Number of atoms          : 4230 (10021 expanded)
%              Number of equality atoms :  193 (1317 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f185,f190,f197,f206,f257,f266,f276,f412,f418,f450,f451,f466,f582,f634,f635,f642,f672,f692,f704,f713,f715,f731,f756,f768,f821,f832,f848,f858,f917,f933,f953,f963,f984,f1020,f1225,f1230,f1262,f1280,f1303,f1311,f1333,f1659,f1671,f1678,f1699,f1704,f1712,f1860,f1875,f2177,f2276,f2310,f2316,f2321,f2336,f2379,f2394,f2395,f2424,f2436,f2611,f2627,f2639,f2658,f2721,f3020,f3025,f3035,f3036,f3040,f3102,f3127,f3142,f3161,f3175,f3219,f3320,f3338,f3354,f3395,f3723,f3733,f6015,f6019,f6031,f6118,f6134,f6222,f6258,f6259,f6273,f6341,f6346,f6380])).

fof(f6380,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | k1_xboole_0 != k1_relat_1(sK2)
    | u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6346,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6341,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_45
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | ~ spl6_120
    | ~ spl6_121
    | spl6_122 ),
    inference(avatar_contradiction_clause,[],[f6340])).

fof(f6340,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_45
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | ~ spl6_120
    | ~ spl6_121
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6339,f2619])).

fof(f2619,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f2617])).

fof(f2617,plain,
    ( spl6_121
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f6339,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_45
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | ~ spl6_120
    | spl6_122 ),
    inference(forward_demodulation,[],[f6338,f847])).

fof(f847,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f845])).

fof(f845,plain,
    ( spl6_45
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f6338,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_45
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | ~ spl6_120
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6337,f2610])).

fof(f2610,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_120 ),
    inference(avatar_component_clause,[],[f2608])).

fof(f2608,plain,
    ( spl6_120
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f6337,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_45
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | spl6_122 ),
    inference(forward_demodulation,[],[f6336,f847])).

fof(f6336,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | ~ spl6_85
    | ~ spl6_93
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6335,f1805])).

fof(f1805,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f1803,plain,
    ( spl6_93
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f6335,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | ~ spl6_85
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6334,f1711])).

fof(f1711,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f1709,plain,
    ( spl6_85
  <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f6334,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6333,f73])).

fof(f73,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f6333,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6332,f73])).

fof(f6332,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6331,f581])).

fof(f581,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f579])).

fof(f579,plain,
    ( spl6_22
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f6331,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_84
    | spl6_122 ),
    inference(subsumption_resolution,[],[f6315,f1703])).

fof(f1703,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f1701])).

fof(f1701,plain,
    ( spl6_84
  <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f6315,plain,
    ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | spl6_122 ),
    inference(resolution,[],[f178,f2625])).

fof(f2625,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_122 ),
    inference(avatar_component_clause,[],[f2624])).

fof(f2624,plain,
    ( spl6_122
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).

fof(f178,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f174,f156])).

fof(f156,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f174,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_5 ),
    inference(resolution,[],[f161,f131])).

fof(f131,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
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
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f161,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl6_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f6273,plain,
    ( spl6_93
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120
    | ~ spl6_129
    | spl6_136 ),
    inference(avatar_split_clause,[],[f6249,f3099,f3032,f2608,f1542,f579,f203,f159,f154,f149,f144,f1803])).

fof(f144,plain,
    ( spl6_2
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f149,plain,
    ( spl6_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f203,plain,
    ( spl6_10
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f1542,plain,
    ( spl6_74
  <=> v5_pre_topc(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f3032,plain,
    ( spl6_129
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).

fof(f3099,plain,
    ( spl6_136
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).

fof(f6249,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120
    | ~ spl6_129
    | spl6_136 ),
    inference(subsumption_resolution,[],[f6248,f2610])).

fof(f6248,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120
    | ~ spl6_129
    | spl6_136 ),
    inference(forward_demodulation,[],[f6142,f6151])).

fof(f6151,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_129
    | spl6_136 ),
    inference(subsumption_resolution,[],[f6135,f3100])).

fof(f3100,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | spl6_136 ),
    inference(avatar_component_clause,[],[f3099])).

fof(f6135,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_129 ),
    inference(subsumption_resolution,[],[f3037,f73])).

fof(f3037,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_129 ),
    inference(resolution,[],[f3034,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f3034,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_129 ),
    inference(avatar_component_clause,[],[f3032])).

fof(f6142,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f6074,f205])).

fof(f205,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f203])).

fof(f6074,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f6073,f205])).

fof(f6073,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74
    | ~ spl6_120 ),
    inference(subsumption_resolution,[],[f6072,f2610])).

fof(f6072,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_74 ),
    inference(forward_demodulation,[],[f6071,f205])).

fof(f6071,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f6070,f151])).

fof(f151,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f149])).

fof(f6070,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_74 ),
    inference(subsumption_resolution,[],[f6068,f146])).

fof(f146,plain,
    ( v2_pre_topc(sK1)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f6068,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_74 ),
    inference(resolution,[],[f1544,f2682])).

fof(f2682,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2681,f73])).

fof(f2681,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2680,f73])).

fof(f2680,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(resolution,[],[f180,f581])).

fof(f180,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_1(X7)
        | ~ l1_pre_topc(X6)
        | ~ v2_pre_topc(X6)
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ v5_pre_topc(X7,sK0,X6) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f176,f156])).

fof(f176,plain,
    ( ! [X6,X7] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ v5_pre_topc(X7,sK0,X6) )
    | ~ spl6_5 ),
    inference(resolution,[],[f161,f129])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,(
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
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
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
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f1544,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f6259,plain,
    ( spl6_121
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f6229,f845,f269,f263,f2617])).

fof(f263,plain,
    ( spl6_13
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f269,plain,
    ( spl6_14
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f6229,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f2457,f271])).

fof(f271,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f269])).

fof(f2457,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_13
    | ~ spl6_45 ),
    inference(forward_demodulation,[],[f265,f847])).

fof(f265,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f263])).

fof(f6258,plain,
    ( spl6_45
    | ~ spl6_129
    | spl6_136 ),
    inference(avatar_split_clause,[],[f6151,f3099,f3032,f845])).

fof(f6222,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_121
    | spl6_122
    | ~ spl6_129
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(avatar_contradiction_clause,[],[f6221])).

fof(f6221,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_121
    | spl6_122
    | ~ spl6_129
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f2619,f6147])).

fof(f6147,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | spl6_122
    | ~ spl6_129
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6146,f2625])).

fof(f6146,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_129
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6145,f205])).

fof(f6145,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_129
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6144,f3034])).

fof(f6144,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6125,f205])).

fof(f6125,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6124,f205])).

fof(f6124,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_22
    | ~ spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6123,f3705])).

fof(f3705,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_159 ),
    inference(avatar_component_clause,[],[f3704])).

fof(f3704,plain,
    ( spl6_159
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).

fof(f6123,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_22
    | ~ spl6_139
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f6122,f146])).

fof(f6122,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_22
    | ~ spl6_139
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f6121,f3685])).

fof(f3685,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_156 ),
    inference(avatar_component_clause,[],[f3684])).

fof(f3684,plain,
    ( spl6_156
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).

fof(f6121,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_22
    | ~ spl6_139 ),
    inference(subsumption_resolution,[],[f6120,f151])).

fof(f6120,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_22
    | ~ spl6_139 ),
    inference(resolution,[],[f3159,f5740])).

fof(f5740,plain,
    ( ! [X2,X0,X1] :
        ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f5739,f73])).

fof(f5739,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f5738,f73])).

fof(f5738,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(resolution,[],[f5513,f581])).

fof(f5513,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_funct_1(X11)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(g1_pre_topc(X8,X9))
      | ~ v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10))))
      | ~ v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))))))
      | v5_pre_topc(X11,g1_pre_topc(X8,X9),g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))
      | ~ v5_pre_topc(X11,g1_pre_topc(X8,X9),X10)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ),
    inference(resolution,[],[f129,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(g1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f3159,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_139 ),
    inference(avatar_component_clause,[],[f3158])).

fof(f3158,plain,
    ( spl6_139
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).

fof(f6134,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6118,plain,
    ( spl6_139
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_120
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(avatar_split_clause,[],[f6078,f3124,f3099,f2608,f1661,f1542,f1387,f579,f203,f159,f154,f149,f144,f3158])).

fof(f1387,plain,
    ( spl6_68
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f1661,plain,
    ( spl6_78
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f3124,plain,
    ( spl6_137
  <=> v1_xboole_0(k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).

fof(f6078,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_120
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f6077,f2610])).

fof(f6077,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(forward_demodulation,[],[f6076,f205])).

fof(f6076,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f6075,f146])).

fof(f6075,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f6069,f151])).

fof(f6069,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_74
    | ~ spl6_78
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(resolution,[],[f1544,f5649])).

fof(f5649,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_78
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f3366,f5644])).

fof(f5644,plain,
    ( ! [X0] : v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl6_78 ),
    inference(subsumption_resolution,[],[f5643,f73])).

fof(f5643,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl6_78 ),
    inference(trivial_inequality_removal,[],[f5642])).

fof(f5642,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | v1_funct_2(k1_xboole_0,k1_xboole_0,X0) )
    | ~ spl6_78 ),
    inference(superposition,[],[f5489,f1662])).

fof(f1662,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f1661])).

fof(f5489,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(duplicate_literal_removal,[],[f5488])).

fof(f5488,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0) ) ),
    inference(forward_demodulation,[],[f5486,f123])).

fof(f123,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5486,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X1,k1_xboole_0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ) ),
    inference(superposition,[],[f5396,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f5396,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(forward_demodulation,[],[f125,f123])).

fof(f125,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f3366,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(k1_xboole_0,sK0,X0)
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f3365,f73])).

fof(f3365,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(subsumption_resolution,[],[f3364,f73])).

fof(f3364,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(resolution,[],[f3287,f581])).

fof(f3287,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(forward_demodulation,[],[f3286,f123])).

fof(f3286,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(forward_demodulation,[],[f3256,f3220])).

fof(f3220,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl6_68
    | ~ spl6_137 ),
    inference(resolution,[],[f1388,f3133])).

fof(f3133,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_relat_1(k1_xboole_0) = X0 )
    | ~ spl6_137 ),
    inference(resolution,[],[f3126,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f3126,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_137 ),
    inference(avatar_component_clause,[],[f3124])).

fof(f1388,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f3256,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_68
    | ~ spl6_136
    | ~ spl6_137 ),
    inference(backward_demodulation,[],[f3114,f3220])).

fof(f3114,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2))))
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_136 ),
    inference(forward_demodulation,[],[f3108,f3106])).

fof(f3106,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_136 ),
    inference(subsumption_resolution,[],[f3104,f73])).

fof(f3104,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_136 ),
    inference(superposition,[],[f3101,f107])).

fof(f3101,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_136 ),
    inference(avatar_component_clause,[],[f3099])).

fof(f3108,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_136 ),
    inference(backward_demodulation,[],[f178,f3106])).

fof(f6031,plain,
    ( ~ spl6_10
    | ~ spl6_14
    | ~ spl6_74
    | ~ spl6_122 ),
    inference(avatar_contradiction_clause,[],[f6030])).

fof(f6030,plain,
    ( $false
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_74
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f1544,f6026])).

fof(f6026,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_122 ),
    inference(forward_demodulation,[],[f6025,f271])).

fof(f6025,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_14
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f6024,f2626])).

fof(f2626,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_122 ),
    inference(avatar_component_clause,[],[f2624])).

fof(f6024,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f2477,f205])).

fof(f2477,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f136,f271])).

fof(f136,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f59,f63])).

fof(f63,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f59,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f6019,plain,
    ( k1_xboole_0 != sK2
    | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6015,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | ~ spl6_122
    | ~ spl6_132
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(avatar_contradiction_clause,[],[f6014])).

fof(f6014,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | ~ spl6_122
    | ~ spl6_132
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6013,f2626])).

fof(f6013,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | ~ spl6_132
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6012,f205])).

fof(f6012,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | ~ spl6_132
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6011,f3071])).

fof(f3071,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_132 ),
    inference(avatar_component_clause,[],[f3070])).

fof(f3070,plain,
    ( spl6_132
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).

fof(f6011,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6010,f3394])).

fof(f3394,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_148 ),
    inference(avatar_component_clause,[],[f3392])).

fof(f3392,plain,
    ( spl6_148
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f6010,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6009,f205])).

fof(f6009,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_73
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6008,f1538])).

fof(f1538,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_73 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f1537,plain,
    ( spl6_73
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f6008,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | spl6_139
    | ~ spl6_148
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6007,f3394])).

fof(f6007,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_10
    | ~ spl6_22
    | spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(forward_demodulation,[],[f6006,f205])).

fof(f6006,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_22
    | spl6_139
    | ~ spl6_156
    | ~ spl6_159 ),
    inference(subsumption_resolution,[],[f6005,f3705])).

fof(f6005,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_22
    | spl6_139
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f6004,f146])).

fof(f6004,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_22
    | spl6_139
    | ~ spl6_156 ),
    inference(subsumption_resolution,[],[f6003,f3685])).

fof(f6003,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_3
    | ~ spl6_22
    | spl6_139 ),
    inference(subsumption_resolution,[],[f5992,f151])).

fof(f5992,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(sK1)
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl6_22
    | spl6_139 ),
    inference(resolution,[],[f3160,f5747])).

fof(f5747,plain,
    ( ! [X2,X0,X1] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f5746,f73])).

fof(f5746,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f5745,f73])).

fof(f5745,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(g1_pre_topc(X1,X2))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1))) )
    | ~ spl6_22 ),
    inference(resolution,[],[f5532,f581])).

fof(f5532,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ v1_funct_1(X11)
      | ~ v2_pre_topc(X10)
      | ~ l1_pre_topc(X10)
      | ~ v2_pre_topc(g1_pre_topc(X8,X9))
      | ~ v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10))))
      | ~ v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))))))
      | ~ v5_pre_topc(X11,g1_pre_topc(X8,X9),g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))
      | v5_pre_topc(X11,g1_pre_topc(X8,X9),X10)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8))) ) ),
    inference(resolution,[],[f130,f93])).

fof(f130,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
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
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | X2 != X3
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3160,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | spl6_139 ),
    inference(avatar_component_clause,[],[f3158])).

fof(f3733,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_156 ),
    inference(avatar_contradiction_clause,[],[f3732])).

fof(f3732,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | spl6_156 ),
    inference(subsumption_resolution,[],[f3731,f156])).

fof(f3731,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl6_5
    | spl6_156 ),
    inference(subsumption_resolution,[],[f3730,f161])).

fof(f3730,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl6_156 ),
    inference(resolution,[],[f3686,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f3686,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | spl6_156 ),
    inference(avatar_component_clause,[],[f3684])).

fof(f3723,plain,
    ( ~ spl6_5
    | spl6_159 ),
    inference(avatar_contradiction_clause,[],[f3722])).

fof(f3722,plain,
    ( $false
    | ~ spl6_5
    | spl6_159 ),
    inference(subsumption_resolution,[],[f3717,f161])).

fof(f3717,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_159 ),
    inference(resolution,[],[f3706,f75])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3706,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl6_159 ),
    inference(avatar_component_clause,[],[f3704])).

fof(f3395,plain,
    ( spl6_148
    | ~ spl6_68
    | ~ spl6_137
    | ~ spl6_138 ),
    inference(avatar_split_clause,[],[f3265,f3139,f3124,f1387,f3392])).

fof(f3139,plain,
    ( spl6_138
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).

fof(f3265,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl6_68
    | ~ spl6_137
    | ~ spl6_138 ),
    inference(backward_demodulation,[],[f3141,f3220])).

fof(f3141,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)
    | ~ spl6_138 ),
    inference(avatar_component_clause,[],[f3139])).

fof(f3354,plain,
    ( spl6_78
    | ~ spl6_68
    | ~ spl6_137 ),
    inference(avatar_split_clause,[],[f3220,f3124,f1387,f1661])).

fof(f3338,plain,
    ( spl6_132
    | ~ spl6_68
    | ~ spl6_128
    | ~ spl6_137 ),
    inference(avatar_split_clause,[],[f3248,f3124,f3022,f1387,f3070])).

fof(f3022,plain,
    ( spl6_128
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).

fof(f3248,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_68
    | ~ spl6_128
    | ~ spl6_137 ),
    inference(backward_demodulation,[],[f3024,f3220])).

fof(f3024,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_128 ),
    inference(avatar_component_clause,[],[f3022])).

fof(f3320,plain,
    ( ~ spl6_14
    | spl6_46 ),
    inference(avatar_contradiction_clause,[],[f3319])).

fof(f3319,plain,
    ( $false
    | ~ spl6_14
    | spl6_46 ),
    inference(subsumption_resolution,[],[f3318,f71])).

fof(f71,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3318,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | ~ spl6_14
    | spl6_46 ),
    inference(forward_demodulation,[],[f857,f271])).

fof(f857,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f855])).

fof(f855,plain,
    ( spl6_46
  <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f3219,plain,
    ( spl6_68
    | ~ spl6_137 ),
    inference(avatar_split_clause,[],[f3201,f3124,f1387])).

fof(f3201,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl6_137 ),
    inference(resolution,[],[f3134,f73])).

fof(f3134,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_relat_1(k1_xboole_0))))
        | v1_xboole_0(X1) )
    | ~ spl6_137 ),
    inference(resolution,[],[f3126,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

fof(f3175,plain,
    ( ~ spl6_141
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_22
    | ~ spl6_84
    | ~ spl6_85
    | spl6_93
    | ~ spl6_122 ),
    inference(avatar_split_clause,[],[f2941,f2624,f1803,f1709,f1701,f579,f269,f263,f159,f154,f3172])).

fof(f3172,plain,
    ( spl6_141
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).

fof(f2941,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_13
    | ~ spl6_14
    | ~ spl6_22
    | ~ spl6_84
    | ~ spl6_85
    | spl6_93
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f2732,f2938])).

fof(f2938,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f265,f271])).

fof(f2732,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_84
    | ~ spl6_85
    | spl6_93
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f2731,f1703])).

fof(f2731,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_85
    | spl6_93
    | ~ spl6_122 ),
    inference(subsumption_resolution,[],[f2730,f2626])).

fof(f2730,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | ~ spl6_85
    | spl6_93 ),
    inference(subsumption_resolution,[],[f2723,f1711])).

fof(f2723,plain,
    ( ~ v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_93 ),
    inference(resolution,[],[f1804,f2673])).

fof(f2673,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2672,f73])).

fof(f2672,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2671,f73])).

fof(f2671,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(resolution,[],[f177,f581])).

fof(f177,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f173,f156])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f161,f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f120])).

fof(f120,plain,(
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
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f1804,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | spl6_93 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f3161,plain,
    ( ~ spl6_139
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120
    | ~ spl6_121 ),
    inference(avatar_split_clause,[],[f2704,f2617,f2608,f1542,f579,f203,f159,f154,f149,f144,f3158])).

fof(f2704,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120
    | ~ spl6_121 ),
    inference(subsumption_resolution,[],[f2703,f2619])).

fof(f2703,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f2702,f205])).

% (18222)Time limit reached!
% (18222)------------------------------
% (18222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18222)Termination reason: Time limit
% (18222)Termination phase: Saturation

% (18222)Memory used [KB]: 3837
% (18222)Time elapsed: 0.800 s
% (18222)------------------------------
% (18222)------------------------------
fof(f2702,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120 ),
    inference(subsumption_resolution,[],[f2701,f2610])).

fof(f2701,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74 ),
    inference(forward_demodulation,[],[f2700,f205])).

fof(f2700,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2699,f151])).

fof(f2699,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2698,f146])).

fof(f2698,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)
    | ~ l1_pre_topc(sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(resolution,[],[f2673,f1543])).

fof(f1543,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | spl6_74 ),
    inference(avatar_component_clause,[],[f1542])).

fof(f3142,plain,
    ( spl6_138
    | ~ spl6_136 ),
    inference(avatar_split_clause,[],[f3106,f3099,f3139])).

fof(f3127,plain,
    ( spl6_137
    | ~ spl6_124 ),
    inference(avatar_split_clause,[],[f3121,f2644,f3124])).

fof(f2644,plain,
    ( spl6_124
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).

fof(f3121,plain,
    ( v1_xboole_0(k1_relat_1(k1_xboole_0))
    | ~ spl6_124 ),
    inference(resolution,[],[f3119,f82])).

fof(f82,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f3119,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
    | ~ spl6_124 ),
    inference(subsumption_resolution,[],[f3118,f73])).

fof(f3118,plain,
    ( ! [X2,X1] :
        ( ~ r2_hidden(X1,k1_relat_1(k1_xboole_0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) )
    | ~ spl6_124 ),
    inference(resolution,[],[f3115,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f3115,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(k1_xboole_0,X0)
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) )
    | ~ spl6_124 ),
    inference(resolution,[],[f2661,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f2661,plain,
    ( ! [X2] :
        ( r1_tarski(k1_relat_1(k1_xboole_0),X2)
        | ~ v4_relat_1(k1_xboole_0,X2) )
    | ~ spl6_124 ),
    inference(resolution,[],[f2645,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f2645,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl6_124 ),
    inference(avatar_component_clause,[],[f2644])).

fof(f3102,plain,
    ( spl6_136
    | ~ spl6_10
    | spl6_38
    | ~ spl6_129 ),
    inference(avatar_split_clause,[],[f3039,f3032,f753,f203,f3099])).

fof(f753,plain,
    ( spl6_38
  <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f3039,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ spl6_10
    | spl6_38
    | ~ spl6_129 ),
    inference(subsumption_resolution,[],[f3038,f73])).

fof(f3038,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | ~ spl6_10
    | spl6_38
    | ~ spl6_129 ),
    inference(subsumption_resolution,[],[f3037,f2932])).

fof(f2932,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | spl6_38 ),
    inference(forward_demodulation,[],[f754,f205])).

fof(f754,plain,
    ( k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f753])).

fof(f3040,plain,
    ( ~ spl6_45
    | ~ spl6_10
    | spl6_38 ),
    inference(avatar_split_clause,[],[f2932,f753,f203,f845])).

fof(f3036,plain,
    ( ~ spl6_78
    | spl6_83 ),
    inference(avatar_split_clause,[],[f3030,f1694,f1661])).

fof(f1694,plain,
    ( spl6_83
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).

fof(f3030,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl6_83 ),
    inference(subsumption_resolution,[],[f3029,f73])).

fof(f3029,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_83 ),
    inference(superposition,[],[f1696,f107])).

fof(f1696,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_83 ),
    inference(avatar_component_clause,[],[f1694])).

fof(f3035,plain,
    ( spl6_129
    | ~ spl6_13
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f2938,f269,f263,f3032])).

fof(f3025,plain,
    ( spl6_128
    | ~ spl6_14
    | ~ spl6_39 ),
    inference(avatar_split_clause,[],[f2937,f802,f269,f3022])).

fof(f802,plain,
    ( spl6_39
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f2937,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_14
    | ~ spl6_39 ),
    inference(forward_demodulation,[],[f804,f271])).

fof(f804,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f802])).

fof(f3020,plain,
    ( ~ spl6_80
    | spl6_123 ),
    inference(avatar_split_clause,[],[f2641,f2636,f1675])).

fof(f1675,plain,
    ( spl6_80
  <=> u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f2636,plain,
    ( spl6_123
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f2641,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0)
    | spl6_123 ),
    inference(subsumption_resolution,[],[f2640,f73])).

fof(f2640,plain,
    ( u1_struct_0(sK0) != k1_relat_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | spl6_123 ),
    inference(superposition,[],[f2638,f107])).

fof(f2638,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | spl6_123 ),
    inference(avatar_component_clause,[],[f2636])).

fof(f2721,plain,
    ( ~ spl6_93
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_45
    | spl6_74
    | ~ spl6_120 ),
    inference(avatar_split_clause,[],[f2713,f2608,f1542,f845,f579,f203,f159,f154,f149,f144,f1803])).

fof(f2713,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_45
    | spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f2712,f205])).

fof(f2712,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_45
    | spl6_74
    | ~ spl6_120 ),
    inference(subsumption_resolution,[],[f2711,f2610])).

fof(f2711,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | ~ spl6_45
    | spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f2710,f847])).

fof(f2710,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120 ),
    inference(forward_demodulation,[],[f2709,f205])).

fof(f2709,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74
    | ~ spl6_120 ),
    inference(subsumption_resolution,[],[f2708,f2610])).

fof(f2708,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10
    | ~ spl6_22
    | spl6_74 ),
    inference(forward_demodulation,[],[f2707,f205])).

fof(f2707,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2706,f151])).

fof(f2706,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2705,f146])).

fof(f2705,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22
    | spl6_74 ),
    inference(resolution,[],[f2676,f1543])).

fof(f2676,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,sK0,X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2675,f73])).

fof(f2675,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f2674,f73])).

fof(f2674,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(resolution,[],[f179,f581])).

fof(f179,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(X5)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f175,f156])).

fof(f175,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_5 ),
    inference(resolution,[],[f161,f130])).

fof(f2658,plain,(
    spl6_124 ),
    inference(avatar_contradiction_clause,[],[f2657])).

fof(f2657,plain,
    ( $false
    | spl6_124 ),
    inference(subsumption_resolution,[],[f2656,f73])).

fof(f2656,plain,
    ( ! [X0,X1] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_124 ),
    inference(resolution,[],[f2646,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f2646,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl6_124 ),
    inference(avatar_component_clause,[],[f2644])).

fof(f2639,plain,
    ( ~ spl6_123
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f2595,f269,f203,f199,f2636])).

fof(f199,plain,
    ( spl6_9
  <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f2595,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0)
    | spl6_9
    | ~ spl6_10
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f583,f271])).

fof(f583,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2)
    | spl6_9
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f200,f205])).

fof(f200,plain,
    ( u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f199])).

fof(f2627,plain,
    ( spl6_122
    | ~ spl6_10
    | ~ spl6_14
    | spl6_74 ),
    inference(avatar_split_clause,[],[f2553,f1542,f269,f203,f2624])).

fof(f2553,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | ~ spl6_14
    | spl6_74 ),
    inference(backward_demodulation,[],[f2476,f205])).

fof(f2476,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2475,f1543])).

fof(f2475,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f2474,f271])).

fof(f2474,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f137,f271])).

fof(f137,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(forward_demodulation,[],[f58,f63])).

fof(f58,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f2611,plain,
    ( spl6_120
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f2456,f269,f254,f2608])).

fof(f254,plain,
    ( spl6_12
  <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f2456,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f256,f271])).

fof(f256,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f254])).

fof(f2436,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_51
    | spl6_74
    | ~ spl6_77
    | ~ spl6_114 ),
    inference(avatar_contradiction_clause,[],[f2435])).

fof(f2435,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_51
    | spl6_74
    | ~ spl6_77
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2434,f2433])).

fof(f2433,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | spl6_74
    | ~ spl6_77
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2432,f1560])).

fof(f1560,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_77 ),
    inference(avatar_component_clause,[],[f1559])).

fof(f1559,plain,
    ( spl6_77
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f2432,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | spl6_74
    | ~ spl6_114 ),
    inference(forward_demodulation,[],[f2431,f755])).

fof(f755,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f753])).

fof(f2431,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | spl6_74
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2430,f73])).

fof(f2430,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | spl6_74
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2429,f151])).

fof(f2429,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | spl6_74
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2428,f146])).

fof(f2428,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | spl6_74
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2427,f581])).

fof(f2427,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_74
    | ~ spl6_114 ),
    inference(subsumption_resolution,[],[f2426,f2320])).

fof(f2320,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_114 ),
    inference(avatar_component_clause,[],[f2318])).

fof(f2318,plain,
    ( spl6_114
  <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).

fof(f2426,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_74 ),
    inference(subsumption_resolution,[],[f2386,f73])).

fof(f2386,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_74 ),
    inference(resolution,[],[f1543,f1459])).

fof(f1459,plain,
    ( ! [X4,X5] :
        ( v5_pre_topc(X5,sK0,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4))
        | ~ v1_funct_1(X5)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1458,f1419])).

fof(f1419,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f321,f499])).

fof(f499,plain,
    ( u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f321,f271])).

fof(f321,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl6_18
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f1458,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4))
        | ~ v1_funct_1(X5)
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1457,f1419])).

fof(f1457,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1425,f1419])).

fof(f1425,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f484,f1419])).

fof(f484,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f483,f321])).

fof(f483,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f482,f321])).

fof(f482,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f481,f321])).

fof(f481,plain,
    ( ! [X4,X5] :
        ( ~ v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
        | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))
        | ~ v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))
        | v5_pre_topc(X5,sK0,X4) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f179,f321])).

fof(f2434,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_51 ),
    inference(forward_demodulation,[],[f915,f271])).

fof(f915,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f914])).

fof(f914,plain,
    ( spl6_51
  <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f2424,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_77
    | ~ spl6_79
    | spl6_110
    | ~ spl6_115 ),
    inference(avatar_contradiction_clause,[],[f2423])).

fof(f2423,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_77
    | ~ spl6_79
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2422,f1560])).

fof(f2422,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_79
    | spl6_110
    | ~ spl6_115 ),
    inference(forward_demodulation,[],[f2421,f755])).

fof(f2421,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_79
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2420,f1670])).

fof(f1670,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_79 ),
    inference(avatar_component_clause,[],[f1668])).

fof(f1668,plain,
    ( spl6_79
  <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).

fof(f2420,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | spl6_110
    | ~ spl6_115 ),
    inference(forward_demodulation,[],[f2419,f755])).

fof(f2419,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_53
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2418,f73])).

fof(f2418,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_53
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2417,f581])).

fof(f2417,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_52
    | ~ spl6_53
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2416,f927])).

fof(f927,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f926])).

fof(f926,plain,
    ( spl6_52
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f2416,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_53
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2415,f931])).

fof(f931,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f930])).

fof(f930,plain,
    ( spl6_53
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f2415,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_110
    | ~ spl6_115 ),
    inference(subsumption_resolution,[],[f2414,f2334])).

fof(f2334,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_115 ),
    inference(avatar_component_clause,[],[f2333])).

fof(f2333,plain,
    ( spl6_115
  <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).

fof(f2414,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_110 ),
    inference(subsumption_resolution,[],[f2398,f73])).

fof(f2398,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | spl6_110 ),
    inference(resolution,[],[f2175,f1452])).

fof(f1452,plain,
    ( ! [X0,X1] :
        ( v5_pre_topc(X1,sK0,X0)
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0)))) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1451,f1419])).

fof(f1451,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1450,f1419])).

fof(f1450,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1449,f1419])).

fof(f1449,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1423,f1419])).

fof(f1423,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f475,f1419])).

fof(f475,plain,
    ( ! [X0,X1] :
        ( ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f474,f321])).

fof(f474,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f473,f321])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f472,f321])).

fof(f472,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f471,f321])).

fof(f471,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f177,f321])).

fof(f2175,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_110 ),
    inference(avatar_component_clause,[],[f2174])).

fof(f2174,plain,
    ( spl6_110
  <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).

fof(f2395,plain,
    ( ~ spl6_110
    | ~ spl6_14
    | spl6_51 ),
    inference(avatar_split_clause,[],[f1942,f914,f269,f2174])).

fof(f1942,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | spl6_51 ),
    inference(forward_demodulation,[],[f916,f271])).

fof(f916,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_51 ),
    inference(avatar_component_clause,[],[f914])).

fof(f2394,plain,
    ( spl6_115
    | ~ spl6_14
    | ~ spl6_18
    | spl6_74 ),
    inference(avatar_split_clause,[],[f2381,f1542,f319,f269,f2333])).

fof(f2381,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_18
    | spl6_74 ),
    inference(subsumption_resolution,[],[f1944,f1543])).

fof(f1944,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,sK1)
    | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1943,f271])).

fof(f1943,plain,
    ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f470,f271])).

fof(f470,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f137,f321])).

fof(f2379,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_110
    | spl6_115 ),
    inference(avatar_contradiction_clause,[],[f2378])).

fof(f2378,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_77
    | ~ spl6_79
    | ~ spl6_110
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2377,f1560])).

fof(f2377,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_79
    | ~ spl6_110
    | spl6_115 ),
    inference(forward_demodulation,[],[f2376,f755])).

fof(f2376,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_79
    | ~ spl6_110
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2375,f1670])).

fof(f2375,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_38
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_110
    | spl6_115 ),
    inference(forward_demodulation,[],[f2374,f755])).

fof(f2374,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_53
    | ~ spl6_110
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2373,f2176])).

fof(f2176,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_110 ),
    inference(avatar_component_clause,[],[f2174])).

fof(f2373,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_52
    | ~ spl6_53
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2372,f927])).

fof(f2372,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | ~ spl6_53
    | spl6_115 ),
    inference(subsumption_resolution,[],[f2371,f931])).

fof(f2371,plain,
    ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22
    | spl6_115 ),
    inference(resolution,[],[f1790,f2335])).

fof(f2335,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_115 ),
    inference(avatar_component_clause,[],[f2333])).

fof(f1790,plain,
    ( ! [X0] :
        ( v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1789,f73])).

fof(f1789,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f1788,f73])).

fof(f1788,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0)
        | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0))))
        | ~ v5_pre_topc(k1_xboole_0,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_22 ),
    inference(resolution,[],[f1456,f581])).

fof(f1456,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2))))
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1455,f1419])).

fof(f1455,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1454,f1419])).

fof(f1454,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1453,f1419])).

fof(f1453,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f1424,f1419])).

fof(f1424,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f480,f1419])).

fof(f480,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f479,f321])).

fof(f479,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f478,f321])).

fof(f478,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f477,f321])).

fof(f477,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f476,f321])).

fof(f476,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f178,f321])).

fof(f2336,plain,
    ( ~ spl6_115
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_18
    | spl6_31 ),
    inference(avatar_split_clause,[],[f1490,f710,f319,f269,f182,f2333])).

fof(f182,plain,
    ( spl6_6
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f710,plain,
    ( spl6_31
  <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f1490,plain,
    ( ~ v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_18
    | spl6_31 ),
    inference(backward_demodulation,[],[f1430,f1471])).

fof(f1471,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f184,f496])).

fof(f496,plain,
    ( k1_xboole_0 = sK3
    | ~ spl6_6
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f184,f271])).

fof(f184,plain,
    ( sK2 = sK3
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f182])).

fof(f1430,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_14
    | ~ spl6_18
    | spl6_31 ),
    inference(backward_demodulation,[],[f712,f1419])).

fof(f712,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f710])).

fof(f2321,plain,
    ( spl6_114
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f2060,f269,f199,f194,f187,f2318])).

fof(f187,plain,
    ( spl6_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f194,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f2060,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_14 ),
    inference(forward_demodulation,[],[f289,f271])).

fof(f289,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f189,f280])).

fof(f280,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(subsumption_resolution,[],[f278,f196])).

fof(f196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f194])).

fof(f278,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_9 ),
    inference(superposition,[],[f201,f107])).

fof(f201,plain,
    ( u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f199])).

fof(f189,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f187])).

fof(f2316,plain,
    ( ~ spl6_78
    | ~ spl6_14
    | spl6_15
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f2301,f319,f273,f269,f1661])).

fof(f273,plain,
    ( spl6_15
  <=> k1_xboole_0 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f2301,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | ~ spl6_14
    | spl6_15
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f452,f271])).

fof(f452,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_15
    | ~ spl6_18 ),
    inference(superposition,[],[f274,f321])).

fof(f274,plain,
    ( k1_xboole_0 != u1_struct_0(sK0)
    | spl6_15 ),
    inference(avatar_component_clause,[],[f273])).

fof(f2310,plain,
    ( ~ spl6_73
    | ~ spl6_14
    | spl6_19 ),
    inference(avatar_split_clause,[],[f2291,f396,f269,f1537])).

fof(f396,plain,
    ( spl6_19
  <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f2291,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_14
    | spl6_19 ),
    inference(forward_demodulation,[],[f397,f271])).

fof(f397,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f396])).

fof(f2276,plain,
    ( spl6_73
    | ~ spl6_83 ),
    inference(avatar_contradiction_clause,[],[f2275])).

fof(f2275,plain,
    ( $false
    | spl6_73
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f1539,f2210])).

fof(f2210,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_83 ),
    inference(subsumption_resolution,[],[f2112,f73])).

fof(f2112,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_83 ),
    inference(trivial_inequality_removal,[],[f2110])).

fof(f2110,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_83 ),
    inference(superposition,[],[f125,f1695])).

fof(f1695,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl6_83 ),
    inference(avatar_component_clause,[],[f1694])).

fof(f1539,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | spl6_73 ),
    inference(avatar_component_clause,[],[f1537])).

fof(f2177,plain,
    ( spl6_110
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1575,f753,f706,f463,f319,f314,f308,f269,f241,f159,f154,f149,f144,f139,f2174])).

fof(f139,plain,
    ( spl6_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f241,plain,
    ( spl6_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f308,plain,
    ( spl6_16
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f314,plain,
    ( spl6_17
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f463,plain,
    ( spl6_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f706,plain,
    ( spl6_30
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f1575,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_16
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f1572,f1574])).

fof(f1574,plain,
    ( v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(forward_demodulation,[],[f309,f271])).

fof(f309,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f1572,plain,
    ( v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1571,f271])).

fof(f1571,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1445,f271])).

fof(f1445,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_14
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f1273,f1419])).

fof(f1273,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f1272,f243])).

fof(f243,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f1272,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1271,f122])).

fof(f122,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f1271,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1270,f755])).

fof(f1270,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1269,f755])).

fof(f1269,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1268,f141])).

fof(f141,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1268,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1267,f151])).

fof(f1267,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1266,f146])).

fof(f1266,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1265,f316])).

fof(f316,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f314])).

fof(f1265,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f1005,f465])).

fof(f465,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f463])).

fof(f1005,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_30 ),
    inference(resolution,[],[f707,f488])).

fof(f488,plain,
    ( ! [X6,X7] :
        ( ~ v5_pre_topc(X7,sK0,X6)
        | ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f487,f321])).

fof(f487,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ v5_pre_topc(X7,sK0,X6) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f486,f321])).

fof(f486,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ v5_pre_topc(X7,sK0,X6) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f485,f321])).

fof(f485,plain,
    ( ! [X6,X7] :
        ( ~ v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6))
        | ~ v2_pre_topc(X6)
        | ~ l1_pre_topc(X6)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6))))
        | ~ v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))
        | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))
        | ~ v5_pre_topc(X7,sK0,X6) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f180,f321])).

fof(f707,plain,
    ( v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f706])).

fof(f1875,plain,
    ( ~ spl6_74
    | ~ spl6_14
    | spl6_30 ),
    inference(avatar_split_clause,[],[f1873,f706,f269,f1542])).

fof(f1873,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK0,sK1)
    | ~ spl6_14
    | spl6_30 ),
    inference(forward_demodulation,[],[f708,f271])).

fof(f708,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f706])).

fof(f1860,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1712,plain,
    ( spl6_85
    | ~ spl6_10
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f1592,f930,f203,f1709])).

fof(f1592,plain,
    ( v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | ~ spl6_53 ),
    inference(backward_demodulation,[],[f931,f205])).

fof(f1704,plain,
    ( spl6_84
    | ~ spl6_10
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f1591,f926,f203,f1701])).

fof(f1591,plain,
    ( l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | ~ spl6_52 ),
    inference(backward_demodulation,[],[f927,f205])).

fof(f1699,plain,
    ( spl6_45
    | ~ spl6_10
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1590,f753,f203,f845])).

fof(f1590,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ spl6_10
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f755,f205])).

fof(f1678,plain,
    ( spl6_80
    | ~ spl6_14
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f499,f319,f269,f1675])).

fof(f1671,plain,
    ( spl6_79
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_63 ),
    inference(avatar_split_clause,[],[f1495,f1308,f319,f269,f182,f1668])).

fof(f1308,plain,
    ( spl6_63
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f1495,plain,
    ( v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_6
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f1446,f1471])).

fof(f1446,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_14
    | ~ spl6_18
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f1310,f1419])).

fof(f1310,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_63 ),
    inference(avatar_component_clause,[],[f1308])).

fof(f1659,plain,
    ( spl6_77
    | ~ spl6_14
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f1574,f308,f269,f1559])).

fof(f1333,plain,
    ( ~ spl6_11
    | spl6_14
    | spl6_19
    | ~ spl6_63 ),
    inference(avatar_contradiction_clause,[],[f1332])).

fof(f1332,plain,
    ( $false
    | ~ spl6_11
    | spl6_14
    | spl6_19
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f1322,f397])).

fof(f1322,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_11
    | spl6_14
    | ~ spl6_63 ),
    inference(backward_demodulation,[],[f1310,f1316])).

fof(f1316,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_11
    | spl6_14
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f1315,f243])).

fof(f1315,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | spl6_14
    | ~ spl6_63 ),
    inference(forward_demodulation,[],[f1314,f122])).

fof(f1314,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | spl6_14
    | ~ spl6_63 ),
    inference(subsumption_resolution,[],[f1312,f270])).

fof(f270,plain,
    ( k1_xboole_0 != sK2
    | spl6_14 ),
    inference(avatar_component_clause,[],[f269])).

fof(f1312,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_63 ),
    inference(resolution,[],[f1310,f126])).

fof(f126,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1311,plain,
    ( spl6_63
    | ~ spl6_27
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1191,f753,f689,f1308])).

fof(f689,plain,
    ( spl6_27
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f1191,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_27
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f691,f755])).

fof(f691,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f689])).

fof(f1303,plain,
    ( ~ spl6_11
    | ~ spl6_34
    | spl6_62 ),
    inference(avatar_contradiction_clause,[],[f1302])).

fof(f1302,plain,
    ( $false
    | ~ spl6_11
    | ~ spl6_34
    | spl6_62 ),
    inference(subsumption_resolution,[],[f1301,f243])).

fof(f1301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_34
    | spl6_62 ),
    inference(forward_demodulation,[],[f1300,f122])).

fof(f1300,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_34
    | spl6_62 ),
    inference(subsumption_resolution,[],[f1294,f1279])).

fof(f1279,plain,
    ( k1_xboole_0 != k1_relat_1(sK2)
    | spl6_62 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f1277,plain,
    ( spl6_62
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1294,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_34 ),
    inference(superposition,[],[f107,f730])).

fof(f730,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f728])).

fof(f728,plain,
    ( spl6_34
  <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f1280,plain,
    ( ~ spl6_62
    | spl6_15
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f452,f319,f273,f1277])).

fof(f1262,plain,
    ( ~ spl6_11
    | spl6_14
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_34
    | spl6_37
    | ~ spl6_38
    | ~ spl6_60 ),
    inference(avatar_contradiction_clause,[],[f1261])).

fof(f1261,plain,
    ( $false
    | ~ spl6_11
    | spl6_14
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_34
    | spl6_37
    | ~ spl6_38
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f1245,f730])).

fof(f1245,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_11
    | spl6_14
    | ~ spl6_15
    | ~ spl6_18
    | spl6_37
    | ~ spl6_38
    | ~ spl6_60 ),
    inference(backward_demodulation,[],[f1212,f1240])).

fof(f1240,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ spl6_11
    | spl6_14
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f1239,f243])).

fof(f1239,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | spl6_14
    | ~ spl6_60 ),
    inference(forward_demodulation,[],[f1238,f122])).

fof(f1238,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | spl6_14
    | ~ spl6_60 ),
    inference(subsumption_resolution,[],[f1236,f270])).

fof(f1236,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_60 ),
    inference(resolution,[],[f1229,f126])).

fof(f1229,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_60 ),
    inference(avatar_component_clause,[],[f1227])).

fof(f1227,plain,
    ( spl6_60
  <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f1212,plain,
    ( u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0,sK2)
    | ~ spl6_15
    | ~ spl6_18
    | spl6_37
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f1211,f1079])).

fof(f1079,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f321,f595])).

fof(f595,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f321,f400])).

fof(f400,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f321,f275])).

fof(f275,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f273])).

fof(f1211,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0,sK2)
    | spl6_37
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f750,f755])).

fof(f750,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | spl6_37 ),
    inference(avatar_component_clause,[],[f749])).

fof(f749,plain,
    ( spl6_37
  <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f1230,plain,
    ( spl6_60
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_27
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1178,f753,f689,f319,f273,f1227])).

fof(f1178,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_27
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f759,f1079])).

fof(f759,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)
    | ~ spl6_27
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f691,f755])).

fof(f1225,plain,
    ( spl6_11
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f358,f273,f194,f241])).

fof(f358,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(forward_demodulation,[],[f334,f123])).

fof(f334,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1))))
    | ~ spl6_8
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f196,f275])).

fof(f1020,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_30
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_53 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_29
    | ~ spl6_30
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f1018,f1012])).

fof(f1012,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f1011,f831])).

fof(f831,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f829])).

fof(f829,plain,
    ( spl6_42
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f1011,plain,
    ( v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1010,f141])).

fof(f1010,plain,
    ( ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1009,f151])).

fof(f1009,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1008,f146])).

fof(f1008,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1007,f316])).

fof(f1007,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_21
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1006,f465])).

fof(f1006,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_30
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1005,f820])).

fof(f820,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f818])).

fof(f818,plain,
    ( spl6_41
  <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f1018,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f1017,f141])).

fof(f1017,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_52
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f1016,f927])).

fof(f1016,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | ~ spl6_53 ),
    inference(subsumption_resolution,[],[f1015,f931])).

fof(f1015,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f1014,f831])).

fof(f1014,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37
    | ~ spl6_41 ),
    inference(subsumption_resolution,[],[f1013,f820])).

fof(f1013,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | spl6_31
    | ~ spl6_37 ),
    inference(resolution,[],[f712,f797])).

fof(f797,plain,
    ( ! [X2,X3] :
        ( v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f792,f782])).

fof(f782,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(subsumption_resolution,[],[f780,f703])).

fof(f703,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f701])).

fof(f701,plain,
    ( spl6_29
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f780,plain,
    ( k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_37 ),
    inference(superposition,[],[f751,f107])).

fof(f751,plain,
    ( u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f749])).

fof(f792,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f784])).

fof(f784,plain,
    ( ! [X2,X3] :
        ( ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2))))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2))))
        | ~ v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2))
        | ~ v2_pre_topc(X2)
        | ~ l1_pre_topc(X2)
        | ~ v1_funct_1(X3)
        | ~ v5_pre_topc(X3,sK0,X2) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f480,f782])).

fof(f984,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_53 ),
    inference(avatar_contradiction_clause,[],[f983])).

fof(f983,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_53 ),
    inference(subsumption_resolution,[],[f982,f146])).

fof(f982,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ spl6_3
    | spl6_53 ),
    inference(subsumption_resolution,[],[f981,f151])).

fof(f981,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl6_53 ),
    inference(resolution,[],[f932,f77])).

fof(f932,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_53 ),
    inference(avatar_component_clause,[],[f930])).

fof(f963,plain,
    ( ~ spl6_3
    | spl6_57 ),
    inference(avatar_contradiction_clause,[],[f962])).

fof(f962,plain,
    ( $false
    | ~ spl6_3
    | spl6_57 ),
    inference(subsumption_resolution,[],[f958,f151])).

fof(f958,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_57 ),
    inference(resolution,[],[f952,f75])).

fof(f952,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl6_57 ),
    inference(avatar_component_clause,[],[f950])).

fof(f950,plain,
    ( spl6_57
  <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f953,plain,
    ( ~ spl6_57
    | spl6_52 ),
    inference(avatar_split_clause,[],[f939,f926,f950])).

fof(f939,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))
    | spl6_52 ),
    inference(resolution,[],[f928,f93])).

fof(f928,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl6_52 ),
    inference(avatar_component_clause,[],[f926])).

fof(f933,plain,
    ( ~ spl6_52
    | ~ spl6_53
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | spl6_51 ),
    inference(avatar_split_clause,[],[f924,f914,f829,f818,f749,f710,f701,f319,f159,f154,f139,f930,f926])).

fof(f924,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_31
    | ~ spl6_37
    | ~ spl6_41
    | ~ spl6_42
    | spl6_51 ),
    inference(subsumption_resolution,[],[f923,f820])).

fof(f923,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_31
    | ~ spl6_37
    | ~ spl6_42
    | spl6_51 ),
    inference(subsumption_resolution,[],[f922,f831])).

fof(f922,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_31
    | ~ spl6_37
    | spl6_51 ),
    inference(subsumption_resolution,[],[f919,f711])).

fof(f711,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f710])).

fof(f919,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37
    | spl6_51 ),
    inference(resolution,[],[f916,f853])).

fof(f853,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,X0)
        | ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) )
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(resolution,[],[f795,f141])).

fof(f795,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f794])).

fof(f794,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f793,f782])).

fof(f793,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(duplicate_literal_removal,[],[f783])).

fof(f783,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | v5_pre_topc(X1,sK0,X0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f475,f782])).

fof(f917,plain,
    ( ~ spl6_51
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(avatar_split_clause,[],[f911,f829,f818,f706,f463,f319,f314,f159,f154,f149,f144,f139,f914])).

fof(f911,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30
    | ~ spl6_41
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f910,f820])).

fof(f910,plain,
    ( ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f909,f831])).

fof(f909,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f908,f151])).

fof(f908,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f907,f146])).

fof(f907,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_17
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f906,f316])).

fof(f906,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | ~ spl6_21
    | spl6_30 ),
    inference(subsumption_resolution,[],[f903,f465])).

fof(f903,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18
    | spl6_30 ),
    inference(resolution,[],[f868,f708])).

fof(f868,plain,
    ( ! [X0] :
        ( v5_pre_topc(sK2,sK0,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
        | ~ v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) )
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_18 ),
    inference(resolution,[],[f484,f141])).

fof(f858,plain,
    ( ~ spl6_46
    | spl6_44 ),
    inference(avatar_split_clause,[],[f849,f841,f855])).

fof(f841,plain,
    ( spl6_44
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f849,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))
    | spl6_44 ),
    inference(resolution,[],[f843,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f843,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl6_44 ),
    inference(avatar_component_clause,[],[f841])).

fof(f848,plain,
    ( ~ spl6_44
    | spl6_45
    | spl6_39 ),
    inference(avatar_split_clause,[],[f811,f802,f845,f841])).

fof(f811,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl6_39 ),
    inference(subsumption_resolution,[],[f810,f107])).

fof(f810,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))
    | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))
    | spl6_39 ),
    inference(resolution,[],[f803,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f803,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f802])).

fof(f832,plain,
    ( spl6_42
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f788,f749,f701,f829])).

fof(f788,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f703,f782])).

fof(f821,plain,
    ( spl6_41
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f787,f749,f701,f689,f818])).

fof(f787,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_27
    | ~ spl6_29
    | ~ spl6_37 ),
    inference(backward_demodulation,[],[f691,f782])).

fof(f768,plain,
    ( spl6_11
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(avatar_contradiction_clause,[],[f767])).

fof(f767,plain,
    ( $false
    | spl6_11
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(subsumption_resolution,[],[f766,f242])).

fof(f242,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f241])).

fof(f766,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f760,f122])).

fof(f760,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)))
    | ~ spl6_29
    | ~ spl6_38 ),
    inference(backward_demodulation,[],[f703,f755])).

fof(f756,plain,
    ( spl6_37
    | spl6_38
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f699,f689,f319,f753,f749])).

fof(f699,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ spl6_18
    | ~ spl6_27 ),
    inference(subsumption_resolution,[],[f698,f467])).

fof(f467,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f133,f321])).

fof(f133,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(forward_demodulation,[],[f62,f63])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) ),
    inference(cnf_transformation,[],[f30])).

fof(f698,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))
    | ~ spl6_27 ),
    inference(resolution,[],[f691,f115])).

fof(f731,plain,
    ( spl6_34
    | ~ spl6_11
    | ~ spl6_19 ),
    inference(avatar_split_clause,[],[f643,f396,f241,f728])).

fof(f643,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f636,f122])).

fof(f636,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_19 ),
    inference(resolution,[],[f398,f124])).

fof(f124,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f398,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f396])).

fof(f715,plain,
    ( spl6_31
    | ~ spl6_18
    | spl6_30 ),
    inference(avatar_split_clause,[],[f714,f706,f319,f710])).

fof(f714,plain,
    ( v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl6_18
    | spl6_30 ),
    inference(subsumption_resolution,[],[f470,f708])).

fof(f713,plain,
    ( ~ spl6_30
    | ~ spl6_31
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f469,f319,f710,f706])).

fof(f469,plain,
    ( ~ v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f136,f321])).

fof(f704,plain,
    ( spl6_29
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f467,f319,f701])).

fof(f692,plain,
    ( spl6_27
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f468,f319,f689])).

fof(f468,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f134,f321])).

fof(f134,plain,(
    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(forward_demodulation,[],[f61,f63])).

fof(f61,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f672,plain,
    ( spl6_21
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f490,f319,f194,f463])).

fof(f490,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_8
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f196,f321])).

fof(f642,plain,
    ( spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(avatar_contradiction_clause,[],[f641])).

fof(f641,plain,
    ( $false
    | spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f640,f243])).

fof(f640,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(forward_demodulation,[],[f639,f122])).

fof(f639,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18
    | ~ spl6_19 ),
    inference(subsumption_resolution,[],[f636,f608])).

fof(f608,plain,
    ( k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)
    | spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f591,f400])).

fof(f591,plain,
    ( k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2)
    | spl6_9
    | ~ spl6_10
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f583,f321])).

fof(f635,plain,
    ( spl6_19
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(avatar_split_clause,[],[f593,f415,f203,f396])).

fof(f415,plain,
    ( spl6_20
  <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f593,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_10
    | ~ spl6_20 ),
    inference(forward_demodulation,[],[f417,f205])).

fof(f417,plain,
    ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f415])).

fof(f634,plain,
    ( spl6_11
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f239,f203,f194,f241])).

fof(f239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(forward_demodulation,[],[f216,f122])).

fof(f216,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f196,f205])).

fof(f582,plain,
    ( spl6_22
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f493,f269,f139,f579])).

fof(f493,plain,
    ( v1_funct_1(k1_xboole_0)
    | ~ spl6_1
    | ~ spl6_14 ),
    inference(backward_demodulation,[],[f141,f271])).

fof(f466,plain,
    ( spl6_21
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f290,f199,f194,f463])).

fof(f290,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(backward_demodulation,[],[f196,f280])).

fof(f451,plain,
    ( spl6_17
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f289,f199,f194,f187,f314])).

fof(f450,plain,
    ( spl6_18
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f280,f199,f194,f319])).

fof(f418,plain,
    ( spl6_20
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f333,f273,f187,f415])).

fof(f333,plain,
    ( v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f189,f275])).

fof(f412,plain,
    ( ~ spl6_19
    | ~ spl6_15
    | spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f401,f319,f308,f273,f396])).

fof(f401,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)
    | ~ spl6_15
    | spl6_16
    | ~ spl6_18 ),
    inference(backward_demodulation,[],[f310,f400])).

fof(f310,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f276,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f261,f254,f241,f273,f269])).

fof(f261,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f260,f243])).

fof(f260,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f258,f122])).

fof(f258,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ spl6_12 ),
    inference(resolution,[],[f256,f126])).

fof(f266,plain,
    ( spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f208,f203,f263])).

fof(f208,plain,
    ( v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f134,f205])).

fof(f257,plain,
    ( spl6_12
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f215,f203,f187,f254])).

fof(f215,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(backward_demodulation,[],[f189,f205])).

fof(f206,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f192,f187,f203,f199])).

fof(f192,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f191,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f30])).

fof(f191,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_7 ),
    inference(resolution,[],[f189,f115])).

fof(f197,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f66,f194])).

fof(f190,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f65,f187])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f185,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f63,f182])).

fof(f162,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f70,f159])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f157,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f69,f154])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f152,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f68,f149])).

fof(f68,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f147,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f67,f144])).

fof(f67,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f64,f139])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18204)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.50  % (18200)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (18203)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (18228)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.52  % (18206)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (18205)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18202)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18230)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (18215)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (18219)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (18211)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (18224)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.52  % (18209)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (18223)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (18212)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (18216)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (18227)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (18201)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (18229)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (18218)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (18208)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (18226)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (18225)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (18220)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (18213)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (18211)Refutation not found, incomplete strategy% (18211)------------------------------
% 0.21/0.55  % (18211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18211)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18211)Memory used [KB]: 11001
% 0.21/0.55  % (18211)Time elapsed: 0.145 s
% 0.21/0.55  % (18211)------------------------------
% 0.21/0.55  % (18211)------------------------------
% 0.21/0.55  % (18214)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (18217)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (18222)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (18217)Refutation not found, incomplete strategy% (18217)------------------------------
% 0.21/0.55  % (18217)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18210)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (18207)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (18210)Refutation not found, incomplete strategy% (18210)------------------------------
% 0.21/0.56  % (18210)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18217)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18217)Memory used [KB]: 10746
% 0.21/0.56  % (18217)Time elapsed: 0.150 s
% 0.21/0.56  % (18217)------------------------------
% 0.21/0.56  % (18217)------------------------------
% 0.21/0.57  % (18210)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (18210)Memory used [KB]: 10874
% 0.21/0.57  % (18210)Time elapsed: 0.164 s
% 0.21/0.57  % (18210)------------------------------
% 0.21/0.57  % (18210)------------------------------
% 2.06/0.69  % (18344)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.06/0.70  % (18339)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.82/0.73  % (18348)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.42/0.83  % (18205)Time limit reached!
% 3.42/0.83  % (18205)------------------------------
% 3.42/0.83  % (18205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.83  % (18205)Termination reason: Time limit
% 3.42/0.83  
% 3.42/0.83  % (18205)Memory used [KB]: 8315
% 3.42/0.83  % (18205)Time elapsed: 0.430 s
% 3.42/0.83  % (18205)------------------------------
% 3.42/0.83  % (18205)------------------------------
% 3.96/0.91  % (18201)Time limit reached!
% 3.96/0.91  % (18201)------------------------------
% 3.96/0.91  % (18201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.91  % (18212)Time limit reached!
% 3.96/0.91  % (18212)------------------------------
% 3.96/0.91  % (18212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.91  % (18212)Termination reason: Time limit
% 3.96/0.91  
% 3.96/0.91  % (18212)Memory used [KB]: 8187
% 3.96/0.91  % (18212)Time elapsed: 0.507 s
% 3.96/0.91  % (18212)------------------------------
% 3.96/0.91  % (18212)------------------------------
% 3.96/0.92  % (18201)Termination reason: Time limit
% 3.96/0.92  
% 3.96/0.92  % (18201)Memory used [KB]: 7036
% 3.96/0.92  % (18201)Time elapsed: 0.505 s
% 3.96/0.92  % (18201)------------------------------
% 3.96/0.92  % (18201)------------------------------
% 3.96/0.93  % (18200)Time limit reached!
% 3.96/0.93  % (18200)------------------------------
% 3.96/0.93  % (18200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.93  % (18200)Termination reason: Time limit
% 3.96/0.93  
% 3.96/0.93  % (18200)Memory used [KB]: 2942
% 3.96/0.93  % (18200)Time elapsed: 0.520 s
% 3.96/0.93  % (18200)------------------------------
% 3.96/0.93  % (18200)------------------------------
% 3.96/0.97  % (18432)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.92/1.02  % (18207)Time limit reached!
% 4.92/1.02  % (18207)------------------------------
% 4.92/1.02  % (18207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.03  % (18433)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.10/1.03  % (18216)Time limit reached!
% 5.10/1.03  % (18216)------------------------------
% 5.10/1.03  % (18216)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.04  % (18207)Termination reason: Time limit
% 5.10/1.04  % (18207)Termination phase: Saturation
% 5.10/1.04  
% 5.10/1.04  % (18207)Memory used [KB]: 9722
% 5.10/1.04  % (18207)Time elapsed: 0.600 s
% 5.10/1.04  % (18207)------------------------------
% 5.10/1.04  % (18207)------------------------------
% 5.10/1.05  % (18216)Termination reason: Time limit
% 5.10/1.05  % (18216)Termination phase: Saturation
% 5.10/1.05  
% 5.10/1.05  % (18216)Memory used [KB]: 17142
% 5.10/1.05  % (18216)Time elapsed: 0.600 s
% 5.10/1.05  % (18216)------------------------------
% 5.10/1.05  % (18216)------------------------------
% 5.10/1.05  % (18434)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.10/1.05  % (18229)Time limit reached!
% 5.10/1.05  % (18229)------------------------------
% 5.10/1.05  % (18229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.10/1.05  % (18229)Termination reason: Time limit
% 5.10/1.05  
% 5.10/1.05  % (18229)Memory used [KB]: 7291
% 5.10/1.05  % (18229)Time elapsed: 0.622 s
% 5.10/1.05  % (18229)------------------------------
% 5.10/1.05  % (18229)------------------------------
% 5.10/1.05  % (18435)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.80/1.15  % (18436)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 5.80/1.15  % (18437)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 5.80/1.18  % (18438)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.80/1.19  % (18220)Refutation found. Thanks to Tanya!
% 5.80/1.19  % SZS status Theorem for theBenchmark
% 5.80/1.19  % SZS output start Proof for theBenchmark
% 5.80/1.19  fof(f6381,plain,(
% 5.80/1.19    $false),
% 5.80/1.19    inference(avatar_sat_refutation,[],[f142,f147,f152,f157,f162,f185,f190,f197,f206,f257,f266,f276,f412,f418,f450,f451,f466,f582,f634,f635,f642,f672,f692,f704,f713,f715,f731,f756,f768,f821,f832,f848,f858,f917,f933,f953,f963,f984,f1020,f1225,f1230,f1262,f1280,f1303,f1311,f1333,f1659,f1671,f1678,f1699,f1704,f1712,f1860,f1875,f2177,f2276,f2310,f2316,f2321,f2336,f2379,f2394,f2395,f2424,f2436,f2611,f2627,f2639,f2658,f2721,f3020,f3025,f3035,f3036,f3040,f3102,f3127,f3142,f3161,f3175,f3219,f3320,f3338,f3354,f3395,f3723,f3733,f6015,f6019,f6031,f6118,f6134,f6222,f6258,f6259,f6273,f6341,f6346,f6380])).
% 5.80/1.19  fof(f6380,plain,(
% 5.80/1.19    k1_xboole_0 != u1_struct_0(sK0) | k1_xboole_0 != k1_relat_1(sK2) | u1_struct_0(sK0) = k1_relat_1(sK2)),
% 5.80/1.19    introduced(theory_tautology_sat_conflict,[])).
% 5.80/1.19  fof(f6346,plain,(
% 5.80/1.19    k1_xboole_0 != sK2 | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 5.80/1.19    introduced(theory_tautology_sat_conflict,[])).
% 5.80/1.19  fof(f6341,plain,(
% 5.80/1.19    ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_45 | ~spl6_84 | ~spl6_85 | ~spl6_93 | ~spl6_120 | ~spl6_121 | spl6_122),
% 5.80/1.19    inference(avatar_contradiction_clause,[],[f6340])).
% 5.80/1.19  fof(f6340,plain,(
% 5.80/1.19    $false | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_45 | ~spl6_84 | ~spl6_85 | ~spl6_93 | ~spl6_120 | ~spl6_121 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6339,f2619])).
% 5.80/1.19  fof(f2619,plain,(
% 5.80/1.19    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl6_121),
% 5.80/1.19    inference(avatar_component_clause,[],[f2617])).
% 5.80/1.19  fof(f2617,plain,(
% 5.80/1.19    spl6_121 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).
% 5.80/1.19  fof(f6339,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_45 | ~spl6_84 | ~spl6_85 | ~spl6_93 | ~spl6_120 | spl6_122)),
% 5.80/1.19    inference(forward_demodulation,[],[f6338,f847])).
% 5.80/1.19  fof(f847,plain,(
% 5.80/1.19    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_45),
% 5.80/1.19    inference(avatar_component_clause,[],[f845])).
% 5.80/1.19  fof(f845,plain,(
% 5.80/1.19    spl6_45 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 5.80/1.19  fof(f6338,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_45 | ~spl6_84 | ~spl6_85 | ~spl6_93 | ~spl6_120 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6337,f2610])).
% 5.80/1.19  fof(f2610,plain,(
% 5.80/1.19    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~spl6_120),
% 5.80/1.19    inference(avatar_component_clause,[],[f2608])).
% 5.80/1.19  fof(f2608,plain,(
% 5.80/1.19    spl6_120 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 5.80/1.19  fof(f6337,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_45 | ~spl6_84 | ~spl6_85 | ~spl6_93 | spl6_122)),
% 5.80/1.19    inference(forward_demodulation,[],[f6336,f847])).
% 5.80/1.19  fof(f6336,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | ~spl6_85 | ~spl6_93 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6335,f1805])).
% 5.80/1.19  fof(f1805,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_93),
% 5.80/1.19    inference(avatar_component_clause,[],[f1803])).
% 5.80/1.19  fof(f1803,plain,(
% 5.80/1.19    spl6_93 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 5.80/1.19  fof(f6335,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | ~spl6_85 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6334,f1711])).
% 5.80/1.19  fof(f1711,plain,(
% 5.80/1.19    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_85),
% 5.80/1.19    inference(avatar_component_clause,[],[f1709])).
% 5.80/1.19  fof(f1709,plain,(
% 5.80/1.19    spl6_85 <=> v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 5.80/1.19  fof(f6334,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6333,f73])).
% 5.80/1.19  fof(f73,plain,(
% 5.80/1.19    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 5.80/1.19    inference(cnf_transformation,[],[f9])).
% 5.80/1.19  fof(f9,axiom,(
% 5.80/1.19    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 5.80/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 5.80/1.19  fof(f6333,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6332,f73])).
% 5.80/1.19  fof(f6332,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6331,f581])).
% 5.80/1.19  fof(f581,plain,(
% 5.80/1.19    v1_funct_1(k1_xboole_0) | ~spl6_22),
% 5.80/1.19    inference(avatar_component_clause,[],[f579])).
% 5.80/1.19  fof(f579,plain,(
% 5.80/1.19    spl6_22 <=> v1_funct_1(k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 5.80/1.19  fof(f6331,plain,(
% 5.80/1.19    ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_84 | spl6_122)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6315,f1703])).
% 5.80/1.19  fof(f1703,plain,(
% 5.80/1.19    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_84),
% 5.80/1.19    inference(avatar_component_clause,[],[f1701])).
% 5.80/1.19  fof(f1701,plain,(
% 5.80/1.19    spl6_84 <=> l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 5.80/1.19  fof(f6315,plain,(
% 5.80/1.19    ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | spl6_122)),
% 5.80/1.19    inference(resolution,[],[f178,f2625])).
% 5.80/1.19  fof(f2625,plain,(
% 5.80/1.19    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_122),
% 5.80/1.19    inference(avatar_component_clause,[],[f2624])).
% 5.80/1.19  fof(f2624,plain,(
% 5.80/1.19    spl6_122 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_122])])).
% 5.80/1.19  fof(f178,plain,(
% 5.80/1.19    ( ! [X2,X3] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5)),
% 5.80/1.19    inference(subsumption_resolution,[],[f174,f156])).
% 5.80/1.19  fof(f156,plain,(
% 5.80/1.19    v2_pre_topc(sK0) | ~spl6_4),
% 5.80/1.19    inference(avatar_component_clause,[],[f154])).
% 5.80/1.19  fof(f154,plain,(
% 5.80/1.19    spl6_4 <=> v2_pre_topc(sK0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 5.80/1.19  fof(f174,plain,(
% 5.80/1.19    ( ! [X2,X3] : (~v2_pre_topc(sK0) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v5_pre_topc(X3,sK0,X2)) ) | ~spl6_5),
% 5.80/1.19    inference(resolution,[],[f161,f131])).
% 5.80/1.19  fof(f131,plain,(
% 5.80/1.19    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.19    inference(duplicate_literal_removal,[],[f119])).
% 5.80/1.19  fof(f119,plain,(
% 5.80/1.19    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.19    inference(equality_resolution,[],[f81])).
% 5.80/1.19  fof(f81,plain,(
% 5.80/1.19    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.19    inference(cnf_transformation,[],[f37])).
% 5.80/1.19  fof(f37,plain,(
% 5.80/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.19    inference(flattening,[],[f36])).
% 5.80/1.19  fof(f36,plain,(
% 5.80/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.19    inference(ennf_transformation,[],[f25])).
% 5.80/1.19  fof(f25,axiom,(
% 5.80/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 5.80/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 5.80/1.19  fof(f161,plain,(
% 5.80/1.19    l1_pre_topc(sK0) | ~spl6_5),
% 5.80/1.19    inference(avatar_component_clause,[],[f159])).
% 5.80/1.19  fof(f159,plain,(
% 5.80/1.19    spl6_5 <=> l1_pre_topc(sK0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 5.80/1.19  fof(f6273,plain,(
% 5.80/1.19    spl6_93 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120 | ~spl6_129 | spl6_136),
% 5.80/1.19    inference(avatar_split_clause,[],[f6249,f3099,f3032,f2608,f1542,f579,f203,f159,f154,f149,f144,f1803])).
% 5.80/1.19  fof(f144,plain,(
% 5.80/1.19    spl6_2 <=> v2_pre_topc(sK1)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 5.80/1.19  fof(f149,plain,(
% 5.80/1.19    spl6_3 <=> l1_pre_topc(sK1)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 5.80/1.19  fof(f203,plain,(
% 5.80/1.19    spl6_10 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 5.80/1.19  fof(f1542,plain,(
% 5.80/1.19    spl6_74 <=> v5_pre_topc(k1_xboole_0,sK0,sK1)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 5.80/1.19  fof(f3032,plain,(
% 5.80/1.19    spl6_129 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_129])])).
% 5.80/1.19  fof(f3099,plain,(
% 5.80/1.19    spl6_136 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_136])])).
% 5.80/1.19  fof(f6249,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120 | ~spl6_129 | spl6_136)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6248,f2610])).
% 5.80/1.19  fof(f6248,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120 | ~spl6_129 | spl6_136)),
% 5.80/1.19    inference(forward_demodulation,[],[f6142,f6151])).
% 5.80/1.19  fof(f6151,plain,(
% 5.80/1.19    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_129 | spl6_136)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6135,f3100])).
% 5.80/1.19  fof(f3100,plain,(
% 5.80/1.19    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | spl6_136),
% 5.80/1.19    inference(avatar_component_clause,[],[f3099])).
% 5.80/1.19  fof(f6135,plain,(
% 5.80/1.19    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl6_129),
% 5.80/1.19    inference(subsumption_resolution,[],[f3037,f73])).
% 5.80/1.19  fof(f3037,plain,(
% 5.80/1.19    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl6_129),
% 5.80/1.19    inference(resolution,[],[f3034,f115])).
% 5.80/1.19  fof(f115,plain,(
% 5.80/1.19    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.80/1.19    inference(cnf_transformation,[],[f55])).
% 5.80/1.19  fof(f55,plain,(
% 5.80/1.19    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.19    inference(flattening,[],[f54])).
% 5.80/1.19  fof(f54,plain,(
% 5.80/1.19    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.19    inference(ennf_transformation,[],[f20])).
% 5.80/1.19  fof(f20,axiom,(
% 5.80/1.19    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 5.80/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 5.80/1.19  fof(f3034,plain,(
% 5.80/1.19    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_129),
% 5.80/1.19    inference(avatar_component_clause,[],[f3032])).
% 5.80/1.19  fof(f6142,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120)),
% 5.80/1.19    inference(forward_demodulation,[],[f6074,f205])).
% 5.80/1.19  fof(f205,plain,(
% 5.80/1.19    k1_xboole_0 = u1_struct_0(sK1) | ~spl6_10),
% 5.80/1.19    inference(avatar_component_clause,[],[f203])).
% 5.80/1.19  fof(f6074,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120)),
% 5.80/1.19    inference(forward_demodulation,[],[f6073,f205])).
% 5.80/1.19  fof(f6073,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74 | ~spl6_120)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6072,f2610])).
% 5.80/1.19  fof(f6072,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_74)),
% 5.80/1.19    inference(forward_demodulation,[],[f6071,f205])).
% 5.80/1.19  fof(f6071,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_74)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6070,f151])).
% 5.80/1.19  fof(f151,plain,(
% 5.80/1.19    l1_pre_topc(sK1) | ~spl6_3),
% 5.80/1.19    inference(avatar_component_clause,[],[f149])).
% 5.80/1.19  fof(f6070,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_74)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6068,f146])).
% 5.80/1.19  fof(f146,plain,(
% 5.80/1.19    v2_pre_topc(sK1) | ~spl6_2),
% 5.80/1.19    inference(avatar_component_clause,[],[f144])).
% 5.80/1.19  fof(f6068,plain,(
% 5.80/1.19    ~v2_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_74)),
% 5.80/1.19    inference(resolution,[],[f1544,f2682])).
% 5.80/1.19  fof(f2682,plain,(
% 5.80/1.19    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,sK0,X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 5.80/1.19    inference(subsumption_resolution,[],[f2681,f73])).
% 5.80/1.19  fof(f2681,plain,(
% 5.80/1.19    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 5.80/1.19    inference(subsumption_resolution,[],[f2680,f73])).
% 5.80/1.19  fof(f2680,plain,(
% 5.80/1.19    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 5.80/1.19    inference(resolution,[],[f180,f581])).
% 5.80/1.19  fof(f180,plain,(
% 5.80/1.19    ( ! [X6,X7] : (~v1_funct_1(X7) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~v5_pre_topc(X7,sK0,X6)) ) | (~spl6_4 | ~spl6_5)),
% 5.80/1.19    inference(subsumption_resolution,[],[f176,f156])).
% 5.80/1.19  fof(f176,plain,(
% 5.80/1.19    ( ! [X6,X7] : (~v2_pre_topc(sK0) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~v5_pre_topc(X7,sK0,X6)) ) | ~spl6_5),
% 5.80/1.19    inference(resolution,[],[f161,f129])).
% 5.80/1.19  fof(f129,plain,(
% 5.80/1.19    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.19    inference(duplicate_literal_removal,[],[f117])).
% 5.80/1.19  fof(f117,plain,(
% 5.80/1.19    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.19    inference(equality_resolution,[],[f79])).
% 5.80/1.19  fof(f79,plain,(
% 5.80/1.19    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.19    inference(cnf_transformation,[],[f35])).
% 5.80/1.19  fof(f35,plain,(
% 5.80/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.19    inference(flattening,[],[f34])).
% 5.80/1.19  fof(f34,plain,(
% 5.80/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.19    inference(ennf_transformation,[],[f26])).
% 5.80/1.19  fof(f26,axiom,(
% 5.80/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).
% 5.80/1.19  fof(f1544,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,sK0,sK1) | ~spl6_74),
% 5.80/1.19    inference(avatar_component_clause,[],[f1542])).
% 5.80/1.19  fof(f6259,plain,(
% 5.80/1.19    spl6_121 | ~spl6_13 | ~spl6_14 | ~spl6_45),
% 5.80/1.19    inference(avatar_split_clause,[],[f6229,f845,f269,f263,f2617])).
% 5.80/1.19  fof(f263,plain,(
% 5.80/1.19    spl6_13 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 5.80/1.19  fof(f269,plain,(
% 5.80/1.19    spl6_14 <=> k1_xboole_0 = sK2),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 5.80/1.19  fof(f6229,plain,(
% 5.80/1.19    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_13 | ~spl6_14 | ~spl6_45)),
% 5.80/1.19    inference(forward_demodulation,[],[f2457,f271])).
% 5.80/1.19  fof(f271,plain,(
% 5.80/1.19    k1_xboole_0 = sK2 | ~spl6_14),
% 5.80/1.19    inference(avatar_component_clause,[],[f269])).
% 5.80/1.19  fof(f2457,plain,(
% 5.80/1.19    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_13 | ~spl6_45)),
% 5.80/1.19    inference(forward_demodulation,[],[f265,f847])).
% 5.80/1.19  fof(f265,plain,(
% 5.80/1.19    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_13),
% 5.80/1.19    inference(avatar_component_clause,[],[f263])).
% 5.80/1.19  fof(f6258,plain,(
% 5.80/1.19    spl6_45 | ~spl6_129 | spl6_136),
% 5.80/1.19    inference(avatar_split_clause,[],[f6151,f3099,f3032,f845])).
% 5.80/1.19  fof(f6222,plain,(
% 5.80/1.19    ~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_121 | spl6_122 | ~spl6_129 | ~spl6_139 | ~spl6_156 | ~spl6_159),
% 5.80/1.19    inference(avatar_contradiction_clause,[],[f6221])).
% 5.80/1.19  fof(f6221,plain,(
% 5.80/1.19    $false | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_121 | spl6_122 | ~spl6_129 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(subsumption_resolution,[],[f2619,f6147])).
% 5.80/1.19  fof(f6147,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | spl6_122 | ~spl6_129 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6146,f2625])).
% 5.80/1.19  fof(f6146,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_129 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(forward_demodulation,[],[f6145,f205])).
% 5.80/1.19  fof(f6145,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_129 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6144,f3034])).
% 5.80/1.19  fof(f6144,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(forward_demodulation,[],[f6125,f205])).
% 5.80/1.19  fof(f6125,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(forward_demodulation,[],[f6124,f205])).
% 5.80/1.19  fof(f6124,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_22 | ~spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6123,f3705])).
% 5.80/1.19  fof(f3705,plain,(
% 5.80/1.19    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl6_159),
% 5.80/1.19    inference(avatar_component_clause,[],[f3704])).
% 5.80/1.19  fof(f3704,plain,(
% 5.80/1.19    spl6_159 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_159])])).
% 5.80/1.19  fof(f6123,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_2 | ~spl6_3 | ~spl6_22 | ~spl6_139 | ~spl6_156)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6122,f146])).
% 5.80/1.19  fof(f6122,plain,(
% 5.80/1.19    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_3 | ~spl6_22 | ~spl6_139 | ~spl6_156)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6121,f3685])).
% 5.80/1.19  fof(f3685,plain,(
% 5.80/1.19    v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_156),
% 5.80/1.19    inference(avatar_component_clause,[],[f3684])).
% 5.80/1.19  fof(f3684,plain,(
% 5.80/1.19    spl6_156 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_156])])).
% 5.80/1.19  fof(f6121,plain,(
% 5.80/1.19    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_3 | ~spl6_22 | ~spl6_139)),
% 5.80/1.19    inference(subsumption_resolution,[],[f6120,f151])).
% 5.80/1.19  fof(f6120,plain,(
% 5.80/1.19    ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_22 | ~spl6_139)),
% 5.80/1.19    inference(resolution,[],[f3159,f5740])).
% 5.80/1.19  fof(f5740,plain,(
% 5.80/1.19    ( ! [X2,X0,X1] : (~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.19    inference(subsumption_resolution,[],[f5739,f73])).
% 5.80/1.19  fof(f5739,plain,(
% 5.80/1.19    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.19    inference(subsumption_resolution,[],[f5738,f73])).
% 5.80/1.19  fof(f5738,plain,(
% 5.80/1.19    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.19    inference(resolution,[],[f5513,f581])).
% 5.80/1.19  fof(f5513,plain,(
% 5.80/1.19    ( ! [X10,X8,X11,X9] : (~v1_funct_1(X11) | ~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(g1_pre_topc(X8,X9)) | ~v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10)))) | ~v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))))) | v5_pre_topc(X11,g1_pre_topc(X8,X9),g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))) | ~v5_pre_topc(X11,g1_pre_topc(X8,X9),X10) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))) )),
% 5.80/1.19    inference(resolution,[],[f129,f93])).
% 5.80/1.19  fof(f93,plain,(
% 5.80/1.19    ( ! [X0,X1] : (l1_pre_topc(g1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 5.80/1.19    inference(cnf_transformation,[],[f43])).
% 5.80/1.19  fof(f43,plain,(
% 5.80/1.19    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 5.80/1.19    inference(ennf_transformation,[],[f22])).
% 5.80/1.19  fof(f22,axiom,(
% 5.80/1.19    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 5.80/1.19    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 5.80/1.19  fof(f3159,plain,(
% 5.80/1.19    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~spl6_139),
% 5.80/1.19    inference(avatar_component_clause,[],[f3158])).
% 5.80/1.19  fof(f3158,plain,(
% 5.80/1.19    spl6_139 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_139])])).
% 5.80/1.19  fof(f6134,plain,(
% 5.80/1.19    k1_xboole_0 != sK2 | k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 5.80/1.19    introduced(theory_tautology_sat_conflict,[])).
% 5.80/1.19  fof(f6118,plain,(
% 5.80/1.19    spl6_139 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_120 | ~spl6_136 | ~spl6_137),
% 5.80/1.19    inference(avatar_split_clause,[],[f6078,f3124,f3099,f2608,f1661,f1542,f1387,f579,f203,f159,f154,f149,f144,f3158])).
% 5.80/1.19  fof(f1387,plain,(
% 5.80/1.19    spl6_68 <=> v1_xboole_0(k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 5.80/1.19  fof(f1661,plain,(
% 5.80/1.19    spl6_78 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).
% 5.80/1.19  fof(f3124,plain,(
% 5.80/1.19    spl6_137 <=> v1_xboole_0(k1_relat_1(k1_xboole_0))),
% 5.80/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_137])])).
% 5.80/1.20  fof(f6078,plain,(
% 5.80/1.20    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_120 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6077,f2610])).
% 5.80/1.20  fof(f6077,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(forward_demodulation,[],[f6076,f205])).
% 5.80/1.20  fof(f6076,plain,(
% 5.80/1.20    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6075,f146])).
% 5.80/1.20  fof(f6075,plain,(
% 5.80/1.20    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6069,f151])).
% 5.80/1.20  fof(f6069,plain,(
% 5.80/1.20    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_74 | ~spl6_78 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(resolution,[],[f1544,f5649])).
% 5.80/1.20  fof(f5649,plain,(
% 5.80/1.20    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,sK0,X0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_78 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3366,f5644])).
% 5.80/1.20  fof(f5644,plain,(
% 5.80/1.20    ( ! [X0] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl6_78),
% 5.80/1.20    inference(subsumption_resolution,[],[f5643,f73])).
% 5.80/1.20  fof(f5643,plain,(
% 5.80/1.20    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl6_78),
% 5.80/1.20    inference(trivial_inequality_removal,[],[f5642])).
% 5.80/1.20  fof(f5642,plain,(
% 5.80/1.20    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl6_78),
% 5.80/1.20    inference(superposition,[],[f5489,f1662])).
% 5.80/1.20  fof(f1662,plain,(
% 5.80/1.20    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl6_78),
% 5.80/1.20    inference(avatar_component_clause,[],[f1661])).
% 5.80/1.20  fof(f5489,plain,(
% 5.80/1.20    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 5.80/1.20    inference(duplicate_literal_removal,[],[f5488])).
% 5.80/1.20  fof(f5488,plain,(
% 5.80/1.20    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0)) )),
% 5.80/1.20    inference(forward_demodulation,[],[f5486,f123])).
% 5.80/1.20  fof(f123,plain,(
% 5.80/1.20    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.80/1.20    inference(equality_resolution,[],[f102])).
% 5.80/1.20  fof(f102,plain,(
% 5.80/1.20    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 5.80/1.20    inference(cnf_transformation,[],[f5])).
% 5.80/1.20  fof(f5,axiom,(
% 5.80/1.20    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.80/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.80/1.20  fof(f5486,plain,(
% 5.80/1.20    ( ! [X0,X1] : (k1_xboole_0 != k1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X1,k1_xboole_0,X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))) )),
% 5.80/1.20    inference(superposition,[],[f5396,f107])).
% 5.80/1.20  fof(f107,plain,(
% 5.80/1.20    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 5.80/1.20    inference(cnf_transformation,[],[f52])).
% 5.80/1.20  fof(f52,plain,(
% 5.80/1.20    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 5.80/1.20    inference(ennf_transformation,[],[f17])).
% 5.80/1.20  fof(f17,axiom,(
% 5.80/1.20    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 5.80/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 5.80/1.20  fof(f5396,plain,(
% 5.80/1.20    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.20    inference(forward_demodulation,[],[f125,f123])).
% 5.80/1.20  fof(f125,plain,(
% 5.80/1.20    ( ! [X2,X1] : (k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_funct_2(X2,k1_xboole_0,X1)) )),
% 5.80/1.20    inference(equality_resolution,[],[f112])).
% 5.80/1.20  fof(f112,plain,(
% 5.80/1.20    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 5.80/1.20    inference(cnf_transformation,[],[f55])).
% 5.80/1.20  fof(f3366,plain,(
% 5.80/1.20    ( ! [X0] : (~v5_pre_topc(k1_xboole_0,sK0,X0) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0))) ) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3365,f73])).
% 5.80/1.20  fof(f3365,plain,(
% 5.80/1.20    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3364,f73])).
% 5.80/1.20  fof(f3364,plain,(
% 5.80/1.20    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(resolution,[],[f3287,f581])).
% 5.80/1.20  fof(f3287,plain,(
% 5.80/1.20    ( ! [X2,X3] : (~v1_funct_1(X3) | ~v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(forward_demodulation,[],[f3286,f123])).
% 5.80/1.20  fof(f3286,plain,(
% 5.80/1.20    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(forward_demodulation,[],[f3256,f3220])).
% 5.80/1.20  fof(f3220,plain,(
% 5.80/1.20    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl6_68 | ~spl6_137)),
% 5.80/1.20    inference(resolution,[],[f1388,f3133])).
% 5.80/1.20  fof(f3133,plain,(
% 5.80/1.20    ( ! [X0] : (~v1_xboole_0(X0) | k1_relat_1(k1_xboole_0) = X0) ) | ~spl6_137),
% 5.80/1.20    inference(resolution,[],[f3126,f104])).
% 5.80/1.20  fof(f104,plain,(
% 5.80/1.20    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 5.80/1.20    inference(cnf_transformation,[],[f49])).
% 5.80/1.20  fof(f49,plain,(
% 5.80/1.20    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 5.80/1.20    inference(ennf_transformation,[],[f4])).
% 5.80/1.20  fof(f4,axiom,(
% 5.80/1.20    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 5.80/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 5.80/1.20  fof(f3126,plain,(
% 5.80/1.20    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl6_137),
% 5.80/1.20    inference(avatar_component_clause,[],[f3124])).
% 5.80/1.20  fof(f1388,plain,(
% 5.80/1.20    v1_xboole_0(k1_xboole_0) | ~spl6_68),
% 5.80/1.20    inference(avatar_component_clause,[],[f1387])).
% 5.80/1.20  fof(f3256,plain,(
% 5.80/1.20    ( ! [X2,X3] : (~v1_funct_2(X3,k1_xboole_0,u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2)))) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_68 | ~spl6_136 | ~spl6_137)),
% 5.80/1.20    inference(backward_demodulation,[],[f3114,f3220])).
% 5.80/1.20  fof(f3114,plain,(
% 5.80/1.20    ( ! [X2,X3] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2)))) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_136)),
% 5.80/1.20    inference(forward_demodulation,[],[f3108,f3106])).
% 5.80/1.20  fof(f3106,plain,(
% 5.80/1.20    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl6_136),
% 5.80/1.20    inference(subsumption_resolution,[],[f3104,f73])).
% 5.80/1.20  fof(f3104,plain,(
% 5.80/1.20    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | ~spl6_136),
% 5.80/1.20    inference(superposition,[],[f3101,f107])).
% 5.80/1.20  fof(f3101,plain,(
% 5.80/1.20    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~spl6_136),
% 5.80/1.20    inference(avatar_component_clause,[],[f3099])).
% 5.80/1.20  fof(f3108,plain,(
% 5.80/1.20    ( ! [X2,X3] : (~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(sK0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_136)),
% 5.80/1.20    inference(backward_demodulation,[],[f178,f3106])).
% 5.80/1.20  fof(f6031,plain,(
% 5.80/1.20    ~spl6_10 | ~spl6_14 | ~spl6_74 | ~spl6_122),
% 5.80/1.20    inference(avatar_contradiction_clause,[],[f6030])).
% 5.80/1.20  fof(f6030,plain,(
% 5.80/1.20    $false | (~spl6_10 | ~spl6_14 | ~spl6_74 | ~spl6_122)),
% 5.80/1.20    inference(subsumption_resolution,[],[f1544,f6026])).
% 5.80/1.20  fof(f6026,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_10 | ~spl6_14 | ~spl6_122)),
% 5.80/1.20    inference(forward_demodulation,[],[f6025,f271])).
% 5.80/1.20  fof(f6025,plain,(
% 5.80/1.20    ~v5_pre_topc(sK2,sK0,sK1) | (~spl6_10 | ~spl6_14 | ~spl6_122)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6024,f2626])).
% 5.80/1.20  fof(f2626,plain,(
% 5.80/1.20    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~spl6_122),
% 5.80/1.20    inference(avatar_component_clause,[],[f2624])).
% 5.80/1.20  fof(f6024,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | (~spl6_10 | ~spl6_14)),
% 5.80/1.20    inference(forward_demodulation,[],[f2477,f205])).
% 5.80/1.20  fof(f2477,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~spl6_14),
% 5.80/1.20    inference(forward_demodulation,[],[f136,f271])).
% 5.80/1.20  fof(f136,plain,(
% 5.80/1.20    ~v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.20    inference(forward_demodulation,[],[f59,f63])).
% 5.80/1.20  fof(f63,plain,(
% 5.80/1.20    sK2 = sK3),
% 5.80/1.20    inference(cnf_transformation,[],[f30])).
% 5.80/1.20  fof(f30,plain,(
% 5.80/1.20    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 5.80/1.20    inference(flattening,[],[f29])).
% 5.80/1.20  fof(f29,plain,(
% 5.80/1.20    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 5.80/1.20    inference(ennf_transformation,[],[f28])).
% 5.80/1.20  fof(f28,negated_conjecture,(
% 5.80/1.20    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.20    inference(negated_conjecture,[],[f27])).
% 5.80/1.20  fof(f27,conjecture,(
% 5.80/1.20    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 5.80/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_pre_topc)).
% 5.80/1.20  fof(f59,plain,(
% 5.80/1.20    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1)),
% 5.80/1.20    inference(cnf_transformation,[],[f30])).
% 5.80/1.20  fof(f6019,plain,(
% 5.80/1.20    k1_xboole_0 != sK2 | u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 5.80/1.20    introduced(theory_tautology_sat_conflict,[])).
% 5.80/1.20  fof(f6015,plain,(
% 5.80/1.20    ~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | ~spl6_122 | ~spl6_132 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159),
% 5.80/1.20    inference(avatar_contradiction_clause,[],[f6014])).
% 5.80/1.20  fof(f6014,plain,(
% 5.80/1.20    $false | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | ~spl6_122 | ~spl6_132 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6013,f2626])).
% 5.80/1.20  fof(f6013,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | ~spl6_132 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(forward_demodulation,[],[f6012,f205])).
% 5.80/1.20  fof(f6012,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | ~spl6_132 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6011,f3071])).
% 5.80/1.20  fof(f3071,plain,(
% 5.80/1.20    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_132),
% 5.80/1.20    inference(avatar_component_clause,[],[f3070])).
% 5.80/1.20  fof(f3070,plain,(
% 5.80/1.20    spl6_132 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 5.80/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_132])])).
% 5.80/1.20  fof(f6011,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(forward_demodulation,[],[f6010,f3394])).
% 5.80/1.20  fof(f3394,plain,(
% 5.80/1.20    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl6_148),
% 5.80/1.20    inference(avatar_component_clause,[],[f3392])).
% 5.80/1.20  fof(f3392,plain,(
% 5.80/1.20    spl6_148 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 5.80/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).
% 5.80/1.20  fof(f6010,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(forward_demodulation,[],[f6009,f205])).
% 5.80/1.20  fof(f6009,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | ~spl6_73 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6008,f1538])).
% 5.80/1.20  fof(f1538,plain,(
% 5.80/1.20    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_73),
% 5.80/1.20    inference(avatar_component_clause,[],[f1537])).
% 5.80/1.20  fof(f1537,plain,(
% 5.80/1.20    spl6_73 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 5.80/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 5.80/1.20  fof(f6008,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | spl6_139 | ~spl6_148 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(forward_demodulation,[],[f6007,f3394])).
% 5.80/1.20  fof(f6007,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_10 | ~spl6_22 | spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(forward_demodulation,[],[f6006,f205])).
% 5.80/1.20  fof(f6006,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_22 | spl6_139 | ~spl6_156 | ~spl6_159)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6005,f3705])).
% 5.80/1.20  fof(f6005,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_2 | ~spl6_3 | ~spl6_22 | spl6_139 | ~spl6_156)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6004,f146])).
% 5.80/1.20  fof(f6004,plain,(
% 5.80/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_3 | ~spl6_22 | spl6_139 | ~spl6_156)),
% 5.80/1.20    inference(subsumption_resolution,[],[f6003,f3685])).
% 5.80/1.20  fof(f6003,plain,(
% 5.80/1.20    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_3 | ~spl6_22 | spl6_139)),
% 5.80/1.20    inference(subsumption_resolution,[],[f5992,f151])).
% 5.80/1.20  fof(f5992,plain,(
% 5.80/1.20    ~l1_pre_topc(sK1) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(sK1) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl6_22 | spl6_139)),
% 5.80/1.20    inference(resolution,[],[f3160,f5747])).
% 5.80/1.20  fof(f5747,plain,(
% 5.80/1.20    ( ! [X2,X0,X1] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.20    inference(subsumption_resolution,[],[f5746,f73])).
% 5.80/1.20  fof(f5746,plain,(
% 5.80/1.20    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.20    inference(subsumption_resolution,[],[f5745,f73])).
% 5.80/1.20  fof(f5745,plain,(
% 5.80/1.20    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(g1_pre_topc(X1,X2)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(X0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X1,X2)),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X1)))) ) | ~spl6_22),
% 5.80/1.20    inference(resolution,[],[f5532,f581])).
% 5.80/1.20  fof(f5532,plain,(
% 5.80/1.20    ( ! [X10,X8,X11,X9] : (~v1_funct_1(X11) | ~v2_pre_topc(X10) | ~l1_pre_topc(X10) | ~v2_pre_topc(g1_pre_topc(X8,X9)) | ~v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10)) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(X10)))) | ~v1_funct_2(X11,u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(X8,X9)),u1_struct_0(g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10)))))) | ~v5_pre_topc(X11,g1_pre_topc(X8,X9),g1_pre_topc(u1_struct_0(X10),u1_pre_topc(X10))) | v5_pre_topc(X11,g1_pre_topc(X8,X9),X10) | ~m1_subset_1(X9,k1_zfmisc_1(k1_zfmisc_1(X8)))) )),
% 5.80/1.20    inference(resolution,[],[f130,f93])).
% 5.80/1.20  fof(f130,plain,(
% 5.80/1.20    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.20    inference(duplicate_literal_removal,[],[f118])).
% 5.80/1.20  fof(f118,plain,(
% 5.80/1.20    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1)) )),
% 5.80/1.20    inference(equality_resolution,[],[f78])).
% 5.80/1.20  fof(f78,plain,(
% 5.80/1.20    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | X2 != X3 | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 5.80/1.20    inference(cnf_transformation,[],[f35])).
% 5.80/1.20  fof(f3160,plain,(
% 5.80/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | spl6_139),
% 5.80/1.20    inference(avatar_component_clause,[],[f3158])).
% 5.80/1.20  fof(f3733,plain,(
% 5.80/1.20    ~spl6_4 | ~spl6_5 | spl6_156),
% 5.80/1.20    inference(avatar_contradiction_clause,[],[f3732])).
% 5.80/1.20  fof(f3732,plain,(
% 5.80/1.20    $false | (~spl6_4 | ~spl6_5 | spl6_156)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3731,f156])).
% 5.80/1.20  fof(f3731,plain,(
% 5.80/1.20    ~v2_pre_topc(sK0) | (~spl6_5 | spl6_156)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3730,f161])).
% 5.80/1.20  fof(f3730,plain,(
% 5.80/1.20    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl6_156),
% 5.80/1.20    inference(resolution,[],[f3686,f77])).
% 5.80/1.20  fof(f77,plain,(
% 5.80/1.20    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 5.80/1.20    inference(cnf_transformation,[],[f33])).
% 5.80/1.20  fof(f33,plain,(
% 5.80/1.20    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 5.80/1.20    inference(flattening,[],[f32])).
% 5.80/1.20  fof(f32,plain,(
% 5.80/1.20    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 5.80/1.20    inference(ennf_transformation,[],[f24])).
% 5.80/1.20  fof(f24,axiom,(
% 5.80/1.20    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 5.80/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).
% 5.80/1.20  fof(f3686,plain,(
% 5.80/1.20    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | spl6_156),
% 5.80/1.20    inference(avatar_component_clause,[],[f3684])).
% 5.80/1.20  fof(f3723,plain,(
% 5.80/1.20    ~spl6_5 | spl6_159),
% 5.80/1.20    inference(avatar_contradiction_clause,[],[f3722])).
% 5.80/1.20  fof(f3722,plain,(
% 5.80/1.20    $false | (~spl6_5 | spl6_159)),
% 5.80/1.20    inference(subsumption_resolution,[],[f3717,f161])).
% 5.80/1.20  fof(f3717,plain,(
% 5.80/1.20    ~l1_pre_topc(sK0) | spl6_159),
% 5.80/1.20    inference(resolution,[],[f3706,f75])).
% 6.25/1.20  fof(f75,plain,(
% 6.25/1.20    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 6.25/1.20    inference(cnf_transformation,[],[f31])).
% 6.25/1.20  fof(f31,plain,(
% 6.25/1.20    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.25/1.20    inference(ennf_transformation,[],[f23])).
% 6.25/1.20  fof(f23,axiom,(
% 6.25/1.20    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 6.25/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 6.25/1.20  fof(f3706,plain,(
% 6.25/1.20    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl6_159),
% 6.25/1.20    inference(avatar_component_clause,[],[f3704])).
% 6.25/1.20  fof(f3395,plain,(
% 6.25/1.20    spl6_148 | ~spl6_68 | ~spl6_137 | ~spl6_138),
% 6.25/1.20    inference(avatar_split_clause,[],[f3265,f3139,f3124,f1387,f3392])).
% 6.25/1.20  fof(f3139,plain,(
% 6.25/1.20    spl6_138 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0)),
% 6.25/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_138])])).
% 6.25/1.20  fof(f3265,plain,(
% 6.25/1.20    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | (~spl6_68 | ~spl6_137 | ~spl6_138)),
% 6.25/1.20    inference(backward_demodulation,[],[f3141,f3220])).
% 6.25/1.20  fof(f3141,plain,(
% 6.25/1.20    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relat_1(k1_xboole_0) | ~spl6_138),
% 6.25/1.20    inference(avatar_component_clause,[],[f3139])).
% 6.25/1.20  fof(f3354,plain,(
% 6.25/1.20    spl6_78 | ~spl6_68 | ~spl6_137),
% 6.25/1.20    inference(avatar_split_clause,[],[f3220,f3124,f1387,f1661])).
% 6.25/1.20  fof(f3338,plain,(
% 6.25/1.20    spl6_132 | ~spl6_68 | ~spl6_128 | ~spl6_137),
% 6.25/1.20    inference(avatar_split_clause,[],[f3248,f3124,f3022,f1387,f3070])).
% 6.25/1.20  fof(f3022,plain,(
% 6.25/1.20    spl6_128 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 6.25/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_128])])).
% 6.25/1.20  fof(f3248,plain,(
% 6.25/1.20    v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_68 | ~spl6_128 | ~spl6_137)),
% 6.25/1.20    inference(backward_demodulation,[],[f3024,f3220])).
% 6.25/1.20  fof(f3024,plain,(
% 6.25/1.20    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_128),
% 6.25/1.20    inference(avatar_component_clause,[],[f3022])).
% 6.25/1.20  fof(f3320,plain,(
% 6.25/1.20    ~spl6_14 | spl6_46),
% 6.25/1.20    inference(avatar_contradiction_clause,[],[f3319])).
% 6.25/1.20  fof(f3319,plain,(
% 6.25/1.20    $false | (~spl6_14 | spl6_46)),
% 6.25/1.20    inference(subsumption_resolution,[],[f3318,f71])).
% 6.25/1.20  fof(f71,plain,(
% 6.25/1.20    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.25/1.20    inference(cnf_transformation,[],[f3])).
% 6.25/1.20  fof(f3,axiom,(
% 6.25/1.20    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.25/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.25/1.20  fof(f3318,plain,(
% 6.25/1.20    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | (~spl6_14 | spl6_46)),
% 6.25/1.20    inference(forward_demodulation,[],[f857,f271])).
% 6.25/1.20  fof(f857,plain,(
% 6.25/1.20    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | spl6_46),
% 6.25/1.20    inference(avatar_component_clause,[],[f855])).
% 6.25/1.20  fof(f855,plain,(
% 6.25/1.20    spl6_46 <=> r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))),
% 6.25/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 6.25/1.20  fof(f3219,plain,(
% 6.25/1.20    spl6_68 | ~spl6_137),
% 6.25/1.20    inference(avatar_split_clause,[],[f3201,f3124,f1387])).
% 6.25/1.20  fof(f3201,plain,(
% 6.25/1.20    v1_xboole_0(k1_xboole_0) | ~spl6_137),
% 6.25/1.20    inference(resolution,[],[f3134,f73])).
% 6.25/1.20  fof(f3134,plain,(
% 6.25/1.20    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,k1_relat_1(k1_xboole_0)))) | v1_xboole_0(X1)) ) | ~spl6_137),
% 6.25/1.20    inference(resolution,[],[f3126,f91])).
% 6.25/1.20  fof(f91,plain,(
% 6.25/1.20    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | v1_xboole_0(X2)) )),
% 6.25/1.20    inference(cnf_transformation,[],[f42])).
% 6.25/1.20  fof(f42,plain,(
% 6.25/1.20    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 6.25/1.20    inference(ennf_transformation,[],[f16])).
% 6.25/1.20  fof(f16,axiom,(
% 6.25/1.20    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 6.25/1.20    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).
% 6.25/1.20  fof(f3175,plain,(
% 6.25/1.20    ~spl6_141 | ~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | ~spl6_22 | ~spl6_84 | ~spl6_85 | spl6_93 | ~spl6_122),
% 6.25/1.20    inference(avatar_split_clause,[],[f2941,f2624,f1803,f1709,f1701,f579,f269,f263,f159,f154,f3172])).
% 6.25/1.20  fof(f3172,plain,(
% 6.25/1.20    spl6_141 <=> v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 6.25/1.20    introduced(avatar_definition,[new_symbols(naming,[spl6_141])])).
% 6.25/1.20  fof(f2941,plain,(
% 6.25/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_13 | ~spl6_14 | ~spl6_22 | ~spl6_84 | ~spl6_85 | spl6_93 | ~spl6_122)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2732,f2938])).
% 6.25/1.20  fof(f2938,plain,(
% 6.25/1.20    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_13 | ~spl6_14)),
% 6.25/1.20    inference(forward_demodulation,[],[f265,f271])).
% 6.25/1.20  fof(f2732,plain,(
% 6.25/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_84 | ~spl6_85 | spl6_93 | ~spl6_122)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2731,f1703])).
% 6.25/1.20  fof(f2731,plain,(
% 6.25/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_85 | spl6_93 | ~spl6_122)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2730,f2626])).
% 6.25/1.20  fof(f2730,plain,(
% 6.25/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | ~spl6_85 | spl6_93)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2723,f1711])).
% 6.25/1.20  fof(f2723,plain,(
% 6.25/1.20    ~v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_93)),
% 6.25/1.20    inference(resolution,[],[f1804,f2673])).
% 6.25/1.20  fof(f2673,plain,(
% 6.25/1.20    ( ! [X0] : (v5_pre_topc(k1_xboole_0,sK0,X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | ~l1_pre_topc(X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2672,f73])).
% 6.25/1.20  fof(f2672,plain,(
% 6.25/1.20    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2671,f73])).
% 6.25/1.20  fof(f2671,plain,(
% 6.25/1.20    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.20    inference(resolution,[],[f177,f581])).
% 6.25/1.20  fof(f177,plain,(
% 6.25/1.20    ( ! [X0,X1] : (~v1_funct_1(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5)),
% 6.25/1.20    inference(subsumption_resolution,[],[f173,f156])).
% 6.25/1.20  fof(f173,plain,(
% 6.25/1.20    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | ~spl6_5),
% 6.25/1.20    inference(resolution,[],[f161,f132])).
% 6.25/1.20  fof(f132,plain,(
% 6.25/1.20    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 6.25/1.20    inference(duplicate_literal_removal,[],[f120])).
% 6.25/1.20  fof(f120,plain,(
% 6.25/1.20    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 6.25/1.20    inference(equality_resolution,[],[f80])).
% 6.25/1.20  fof(f80,plain,(
% 6.25/1.20    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 6.25/1.20    inference(cnf_transformation,[],[f37])).
% 6.25/1.20  fof(f1804,plain,(
% 6.25/1.20    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | spl6_93),
% 6.25/1.20    inference(avatar_component_clause,[],[f1803])).
% 6.25/1.20  fof(f3161,plain,(
% 6.25/1.20    ~spl6_139 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120 | ~spl6_121),
% 6.25/1.20    inference(avatar_split_clause,[],[f2704,f2617,f2608,f1542,f579,f203,f159,f154,f149,f144,f3158])).
% 6.25/1.20  fof(f2704,plain,(
% 6.25/1.20    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120 | ~spl6_121)),
% 6.25/1.20    inference(subsumption_resolution,[],[f2703,f2619])).
% 6.25/1.20  fof(f2703,plain,(
% 6.25/1.20    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120)),
% 6.25/1.20    inference(forward_demodulation,[],[f2702,f205])).
% 6.25/1.21  % (18222)Time limit reached!
% 6.25/1.21  % (18222)------------------------------
% 6.25/1.21  % (18222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.25/1.21  % (18222)Termination reason: Time limit
% 6.25/1.21  % (18222)Termination phase: Saturation
% 6.25/1.21  
% 6.25/1.21  % (18222)Memory used [KB]: 3837
% 6.25/1.21  % (18222)Time elapsed: 0.800 s
% 6.25/1.21  % (18222)------------------------------
% 6.25/1.21  % (18222)------------------------------
% 6.25/1.21  fof(f2702,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2701,f2610])).
% 6.25/1.21  fof(f2701,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(forward_demodulation,[],[f2700,f205])).
% 6.25/1.21  fof(f2700,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2699,f151])).
% 6.25/1.21  fof(f2699,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2698,f146])).
% 6.25/1.21  fof(f2698,plain,(
% 6.25/1.21    ~v2_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(sK1)) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),sK1) | ~l1_pre_topc(sK1) | (~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(resolution,[],[f2673,f1543])).
% 6.25/1.21  fof(f1543,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | spl6_74),
% 6.25/1.21    inference(avatar_component_clause,[],[f1542])).
% 6.25/1.21  fof(f3142,plain,(
% 6.25/1.21    spl6_138 | ~spl6_136),
% 6.25/1.21    inference(avatar_split_clause,[],[f3106,f3099,f3139])).
% 6.25/1.21  fof(f3127,plain,(
% 6.25/1.21    spl6_137 | ~spl6_124),
% 6.25/1.21    inference(avatar_split_clause,[],[f3121,f2644,f3124])).
% 6.25/1.21  fof(f2644,plain,(
% 6.25/1.21    spl6_124 <=> v1_relat_1(k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_124])])).
% 6.25/1.21  fof(f3121,plain,(
% 6.25/1.21    v1_xboole_0(k1_relat_1(k1_xboole_0)) | ~spl6_124),
% 6.25/1.21    inference(resolution,[],[f3119,f82])).
% 6.25/1.21  fof(f82,plain,(
% 6.25/1.21    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 6.25/1.21    inference(cnf_transformation,[],[f1])).
% 6.25/1.21  fof(f1,axiom,(
% 6.25/1.21    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 6.25/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 6.25/1.21  fof(f3119,plain,(
% 6.25/1.21    ( ! [X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0))) ) | ~spl6_124),
% 6.25/1.21    inference(subsumption_resolution,[],[f3118,f73])).
% 6.25/1.21  fof(f3118,plain,(
% 6.25/1.21    ( ! [X2,X1] : (~r2_hidden(X1,k1_relat_1(k1_xboole_0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) ) | ~spl6_124),
% 6.25/1.21    inference(resolution,[],[f3115,f108])).
% 6.25/1.21  fof(f108,plain,(
% 6.25/1.21    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.25/1.21    inference(cnf_transformation,[],[f53])).
% 6.25/1.21  fof(f53,plain,(
% 6.25/1.21    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.25/1.21    inference(ennf_transformation,[],[f15])).
% 6.25/1.21  fof(f15,axiom,(
% 6.25/1.21    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.25/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 6.25/1.21  fof(f3115,plain,(
% 6.25/1.21    ( ! [X0] : (~v4_relat_1(k1_xboole_0,X0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | ~spl6_124),
% 6.25/1.21    inference(resolution,[],[f2661,f105])).
% 6.25/1.21  fof(f105,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 6.25/1.21    inference(cnf_transformation,[],[f50])).
% 6.25/1.21  fof(f50,plain,(
% 6.25/1.21    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.25/1.21    inference(ennf_transformation,[],[f13])).
% 6.25/1.21  fof(f13,axiom,(
% 6.25/1.21    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.25/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 6.25/1.21  fof(f2661,plain,(
% 6.25/1.21    ( ! [X2] : (r1_tarski(k1_relat_1(k1_xboole_0),X2) | ~v4_relat_1(k1_xboole_0,X2)) ) | ~spl6_124),
% 6.25/1.21    inference(resolution,[],[f2645,f90])).
% 6.25/1.21  fof(f90,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 6.25/1.21    inference(cnf_transformation,[],[f41])).
% 6.25/1.21  fof(f41,plain,(
% 6.25/1.21    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 6.25/1.21    inference(ennf_transformation,[],[f12])).
% 6.25/1.21  fof(f12,axiom,(
% 6.25/1.21    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 6.25/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 6.25/1.21  fof(f2645,plain,(
% 6.25/1.21    v1_relat_1(k1_xboole_0) | ~spl6_124),
% 6.25/1.21    inference(avatar_component_clause,[],[f2644])).
% 6.25/1.21  fof(f3102,plain,(
% 6.25/1.21    spl6_136 | ~spl6_10 | spl6_38 | ~spl6_129),
% 6.25/1.21    inference(avatar_split_clause,[],[f3039,f3032,f753,f203,f3099])).
% 6.25/1.21  fof(f753,plain,(
% 6.25/1.21    spl6_38 <=> k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 6.25/1.21  fof(f3039,plain,(
% 6.25/1.21    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | (~spl6_10 | spl6_38 | ~spl6_129)),
% 6.25/1.21    inference(subsumption_resolution,[],[f3038,f73])).
% 6.25/1.21  fof(f3038,plain,(
% 6.25/1.21    u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | (~spl6_10 | spl6_38 | ~spl6_129)),
% 6.25/1.21    inference(subsumption_resolution,[],[f3037,f2932])).
% 6.25/1.21  fof(f2932,plain,(
% 6.25/1.21    k1_xboole_0 != u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | spl6_38)),
% 6.25/1.21    inference(forward_demodulation,[],[f754,f205])).
% 6.25/1.21  fof(f754,plain,(
% 6.25/1.21    k1_xboole_0 != u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_38),
% 6.25/1.21    inference(avatar_component_clause,[],[f753])).
% 6.25/1.21  fof(f3040,plain,(
% 6.25/1.21    ~spl6_45 | ~spl6_10 | spl6_38),
% 6.25/1.21    inference(avatar_split_clause,[],[f2932,f753,f203,f845])).
% 6.25/1.21  fof(f3036,plain,(
% 6.25/1.21    ~spl6_78 | spl6_83),
% 6.25/1.21    inference(avatar_split_clause,[],[f3030,f1694,f1661])).
% 6.25/1.21  fof(f1694,plain,(
% 6.25/1.21    spl6_83 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_83])])).
% 6.25/1.21  fof(f3030,plain,(
% 6.25/1.21    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl6_83),
% 6.25/1.21    inference(subsumption_resolution,[],[f3029,f73])).
% 6.25/1.21  fof(f3029,plain,(
% 6.25/1.21    k1_xboole_0 != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | spl6_83),
% 6.25/1.21    inference(superposition,[],[f1696,f107])).
% 6.25/1.21  fof(f1696,plain,(
% 6.25/1.21    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl6_83),
% 6.25/1.21    inference(avatar_component_clause,[],[f1694])).
% 6.25/1.21  fof(f3035,plain,(
% 6.25/1.21    spl6_129 | ~spl6_13 | ~spl6_14),
% 6.25/1.21    inference(avatar_split_clause,[],[f2938,f269,f263,f3032])).
% 6.25/1.21  fof(f3025,plain,(
% 6.25/1.21    spl6_128 | ~spl6_14 | ~spl6_39),
% 6.25/1.21    inference(avatar_split_clause,[],[f2937,f802,f269,f3022])).
% 6.25/1.21  fof(f802,plain,(
% 6.25/1.21    spl6_39 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 6.25/1.21  fof(f2937,plain,(
% 6.25/1.21    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | (~spl6_14 | ~spl6_39)),
% 6.25/1.21    inference(forward_demodulation,[],[f804,f271])).
% 6.25/1.21  fof(f804,plain,(
% 6.25/1.21    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_39),
% 6.25/1.21    inference(avatar_component_clause,[],[f802])).
% 6.25/1.21  fof(f3020,plain,(
% 6.25/1.21    ~spl6_80 | spl6_123),
% 6.25/1.21    inference(avatar_split_clause,[],[f2641,f2636,f1675])).
% 6.25/1.21  fof(f1675,plain,(
% 6.25/1.21    spl6_80 <=> u1_struct_0(sK0) = k1_relat_1(k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).
% 6.25/1.21  fof(f2636,plain,(
% 6.25/1.21    spl6_123 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 6.25/1.21  fof(f2641,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relat_1(k1_xboole_0) | spl6_123),
% 6.25/1.21    inference(subsumption_resolution,[],[f2640,f73])).
% 6.25/1.21  fof(f2640,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relat_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | spl6_123),
% 6.25/1.21    inference(superposition,[],[f2638,f107])).
% 6.25/1.21  fof(f2638,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) | spl6_123),
% 6.25/1.21    inference(avatar_component_clause,[],[f2636])).
% 6.25/1.21  fof(f2721,plain,(
% 6.25/1.21    ~spl6_93 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_45 | spl6_74 | ~spl6_120),
% 6.25/1.21    inference(avatar_split_clause,[],[f2713,f2608,f1542,f845,f579,f203,f159,f154,f149,f144,f1803])).
% 6.25/1.21  fof(f2713,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_45 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(forward_demodulation,[],[f2712,f205])).
% 6.25/1.21  fof(f2712,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_45 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2711,f2610])).
% 6.25/1.21  fof(f2711,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | ~spl6_45 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(forward_demodulation,[],[f2710,f847])).
% 6.25/1.21  fof(f2710,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(forward_demodulation,[],[f2709,f205])).
% 6.25/1.21  fof(f2709,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74 | ~spl6_120)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2708,f2610])).
% 6.25/1.21  fof(f2708,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_10 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(forward_demodulation,[],[f2707,f205])).
% 6.25/1.21  fof(f2707,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2706,f151])).
% 6.25/1.21  fof(f2706,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2705,f146])).
% 6.25/1.21  fof(f2705,plain,(
% 6.25/1.21    ~v2_pre_topc(sK1) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1) | (~spl6_4 | ~spl6_5 | ~spl6_22 | spl6_74)),
% 6.25/1.21    inference(resolution,[],[f2676,f1543])).
% 6.25/1.21  fof(f2676,plain,(
% 6.25/1.21    ( ! [X0] : (v5_pre_topc(k1_xboole_0,sK0,X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2675,f73])).
% 6.25/1.21  fof(f2675,plain,(
% 6.25/1.21    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2674,f73])).
% 6.25/1.21  fof(f2674,plain,(
% 6.25/1.21    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(k1_xboole_0,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_22)),
% 6.25/1.21    inference(resolution,[],[f179,f581])).
% 6.25/1.21  fof(f179,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_1(X5) | ~l1_pre_topc(X4) | ~v2_pre_topc(X4) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5)),
% 6.25/1.21    inference(subsumption_resolution,[],[f175,f156])).
% 6.25/1.21  fof(f175,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | ~spl6_5),
% 6.25/1.21    inference(resolution,[],[f161,f130])).
% 6.25/1.21  fof(f2658,plain,(
% 6.25/1.21    spl6_124),
% 6.25/1.21    inference(avatar_contradiction_clause,[],[f2657])).
% 6.25/1.21  fof(f2657,plain,(
% 6.25/1.21    $false | spl6_124),
% 6.25/1.21    inference(subsumption_resolution,[],[f2656,f73])).
% 6.25/1.21  fof(f2656,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_124),
% 6.25/1.21    inference(resolution,[],[f2646,f106])).
% 6.25/1.21  fof(f106,plain,(
% 6.25/1.21    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.25/1.21    inference(cnf_transformation,[],[f51])).
% 6.25/1.21  fof(f51,plain,(
% 6.25/1.21    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.25/1.21    inference(ennf_transformation,[],[f14])).
% 6.25/1.21  fof(f14,axiom,(
% 6.25/1.21    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.25/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 6.25/1.21  fof(f2646,plain,(
% 6.25/1.21    ~v1_relat_1(k1_xboole_0) | spl6_124),
% 6.25/1.21    inference(avatar_component_clause,[],[f2644])).
% 6.25/1.21  fof(f2639,plain,(
% 6.25/1.21    ~spl6_123 | spl6_9 | ~spl6_10 | ~spl6_14),
% 6.25/1.21    inference(avatar_split_clause,[],[f2595,f269,f203,f199,f2636])).
% 6.25/1.21  fof(f199,plain,(
% 6.25/1.21    spl6_9 <=> u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 6.25/1.21  fof(f2595,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,k1_xboole_0) | (spl6_9 | ~spl6_10 | ~spl6_14)),
% 6.25/1.21    inference(forward_demodulation,[],[f583,f271])).
% 6.25/1.21  fof(f583,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),k1_xboole_0,sK2) | (spl6_9 | ~spl6_10)),
% 6.25/1.21    inference(forward_demodulation,[],[f200,f205])).
% 6.25/1.21  fof(f200,plain,(
% 6.25/1.21    u1_struct_0(sK0) != k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | spl6_9),
% 6.25/1.21    inference(avatar_component_clause,[],[f199])).
% 6.25/1.21  fof(f2627,plain,(
% 6.25/1.21    spl6_122 | ~spl6_10 | ~spl6_14 | spl6_74),
% 6.25/1.21    inference(avatar_split_clause,[],[f2553,f1542,f269,f203,f2624])).
% 6.25/1.21  fof(f2553,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | ~spl6_14 | spl6_74)),
% 6.25/1.21    inference(backward_demodulation,[],[f2476,f205])).
% 6.25/1.21  fof(f2476,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2475,f1543])).
% 6.25/1.21  fof(f2475,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_14),
% 6.25/1.21    inference(forward_demodulation,[],[f2474,f271])).
% 6.25/1.21  fof(f2474,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~spl6_14),
% 6.25/1.21    inference(forward_demodulation,[],[f137,f271])).
% 6.25/1.21  fof(f137,plain,(
% 6.25/1.21    v5_pre_topc(sK2,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 6.25/1.21    inference(forward_demodulation,[],[f58,f63])).
% 6.25/1.21  fof(f58,plain,(
% 6.25/1.21    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1)),
% 6.25/1.21    inference(cnf_transformation,[],[f30])).
% 6.25/1.21  fof(f2611,plain,(
% 6.25/1.21    spl6_120 | ~spl6_12 | ~spl6_14),
% 6.25/1.21    inference(avatar_split_clause,[],[f2456,f269,f254,f2608])).
% 6.25/1.21  fof(f254,plain,(
% 6.25/1.21    spl6_12 <=> v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 6.25/1.21  fof(f2456,plain,(
% 6.25/1.21    v1_funct_2(k1_xboole_0,u1_struct_0(sK0),k1_xboole_0) | (~spl6_12 | ~spl6_14)),
% 6.25/1.21    inference(forward_demodulation,[],[f256,f271])).
% 6.25/1.21  fof(f256,plain,(
% 6.25/1.21    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | ~spl6_12),
% 6.25/1.21    inference(avatar_component_clause,[],[f254])).
% 6.25/1.21  fof(f2436,plain,(
% 6.25/1.21    ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_51 | spl6_74 | ~spl6_77 | ~spl6_114),
% 6.25/1.21    inference(avatar_contradiction_clause,[],[f2435])).
% 6.25/1.21  fof(f2435,plain,(
% 6.25/1.21    $false | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_51 | spl6_74 | ~spl6_77 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2434,f2433])).
% 6.25/1.21  fof(f2433,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | spl6_74 | ~spl6_77 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2432,f1560])).
% 6.25/1.21  fof(f1560,plain,(
% 6.25/1.21    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~spl6_77),
% 6.25/1.21    inference(avatar_component_clause,[],[f1559])).
% 6.25/1.21  fof(f1559,plain,(
% 6.25/1.21    spl6_77 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).
% 6.25/1.21  fof(f2432,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(forward_demodulation,[],[f2431,f755])).
% 6.25/1.21  fof(f755,plain,(
% 6.25/1.21    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_38),
% 6.25/1.21    inference(avatar_component_clause,[],[f753])).
% 6.25/1.21  fof(f2431,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2430,f73])).
% 6.25/1.21  fof(f2430,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2429,f151])).
% 6.25/1.21  fof(f2429,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2428,f146])).
% 6.25/1.21  fof(f2428,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2427,f581])).
% 6.25/1.21  fof(f2427,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_74 | ~spl6_114)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2426,f2320])).
% 6.25/1.21  fof(f2320,plain,(
% 6.25/1.21    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~spl6_114),
% 6.25/1.21    inference(avatar_component_clause,[],[f2318])).
% 6.25/1.21  fof(f2318,plain,(
% 6.25/1.21    spl6_114 <=> v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_114])])).
% 6.25/1.21  fof(f2426,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2386,f73])).
% 6.25/1.21  fof(f2386,plain,(
% 6.25/1.21    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | ~v1_funct_1(k1_xboole_0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_74)),
% 6.25/1.21    inference(resolution,[],[f1543,f1459])).
% 6.25/1.21  fof(f1459,plain,(
% 6.25/1.21    ( ! [X4,X5] : (v5_pre_topc(X5,sK0,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X4)))) | ~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))))))) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1458,f1419])).
% 6.25/1.21  fof(f1419,plain,(
% 6.25/1.21    k1_relat_1(sK2) = k1_relat_1(k1_xboole_0) | (~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(backward_demodulation,[],[f321,f499])).
% 6.25/1.21  fof(f499,plain,(
% 6.25/1.21    u1_struct_0(sK0) = k1_relat_1(k1_xboole_0) | (~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(backward_demodulation,[],[f321,f271])).
% 6.25/1.21  fof(f321,plain,(
% 6.25/1.21    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl6_18),
% 6.25/1.21    inference(avatar_component_clause,[],[f319])).
% 6.25/1.21  fof(f319,plain,(
% 6.25/1.21    spl6_18 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 6.25/1.21  fof(f1458,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X4)))) | ~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1457,f1419])).
% 6.25/1.21  fof(f1457,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1425,f1419])).
% 6.25/1.21  fof(f1425,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_2(X5,k1_relat_1(k1_xboole_0),u1_struct_0(X4)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(backward_demodulation,[],[f484,f1419])).
% 6.25/1.21  fof(f484,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_1(X5) | ~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4)) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f483,f321])).
% 6.25/1.21  fof(f483,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4)) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f482,f321])).
% 6.25/1.21  fof(f482,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X4)))) | ~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4)) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f481,f321])).
% 6.25/1.21  fof(f481,plain,(
% 6.25/1.21    ( ! [X4,X5] : (~v1_funct_2(X5,k1_relat_1(sK2),u1_struct_0(X4)) | ~v2_pre_topc(X4) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4)))))) | ~v5_pre_topc(X5,sK0,g1_pre_topc(u1_struct_0(X4),u1_pre_topc(X4))) | v5_pre_topc(X5,sK0,X4)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f179,f321])).
% 6.25/1.21  fof(f2434,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_51)),
% 6.25/1.21    inference(forward_demodulation,[],[f915,f271])).
% 6.25/1.21  fof(f915,plain,(
% 6.25/1.21    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_51),
% 6.25/1.21    inference(avatar_component_clause,[],[f914])).
% 6.25/1.21  fof(f914,plain,(
% 6.25/1.21    spl6_51 <=> v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 6.25/1.21  fof(f2424,plain,(
% 6.25/1.21    ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_77 | ~spl6_79 | spl6_110 | ~spl6_115),
% 6.25/1.21    inference(avatar_contradiction_clause,[],[f2423])).
% 6.25/1.21  fof(f2423,plain,(
% 6.25/1.21    $false | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_77 | ~spl6_79 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2422,f1560])).
% 6.25/1.21  fof(f2422,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_79 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(forward_demodulation,[],[f2421,f755])).
% 6.25/1.21  fof(f2421,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_79 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2420,f1670])).
% 6.25/1.21  fof(f1670,plain,(
% 6.25/1.21    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~spl6_79),
% 6.25/1.21    inference(avatar_component_clause,[],[f1668])).
% 6.25/1.21  fof(f1668,plain,(
% 6.25/1.21    spl6_79 <=> v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0)),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_79])])).
% 6.25/1.21  fof(f2420,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(forward_demodulation,[],[f2419,f755])).
% 6.25/1.21  fof(f2419,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_52 | ~spl6_53 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2418,f73])).
% 6.25/1.21  fof(f2418,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_52 | ~spl6_53 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2417,f581])).
% 6.25/1.21  fof(f2417,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_52 | ~spl6_53 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2416,f927])).
% 6.25/1.21  fof(f927,plain,(
% 6.25/1.21    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_52),
% 6.25/1.21    inference(avatar_component_clause,[],[f926])).
% 6.25/1.21  fof(f926,plain,(
% 6.25/1.21    spl6_52 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 6.25/1.21  fof(f2416,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_53 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2415,f931])).
% 6.25/1.21  fof(f931,plain,(
% 6.25/1.21    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_53),
% 6.25/1.21    inference(avatar_component_clause,[],[f930])).
% 6.25/1.21  fof(f930,plain,(
% 6.25/1.21    spl6_53 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 6.25/1.21  fof(f2415,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_110 | ~spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2414,f2334])).
% 6.25/1.21  fof(f2334,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_115),
% 6.25/1.21    inference(avatar_component_clause,[],[f2333])).
% 6.25/1.21  fof(f2333,plain,(
% 6.25/1.21    spl6_115 <=> v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_115])])).
% 6.25/1.21  fof(f2414,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_110)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2398,f73])).
% 6.25/1.21  fof(f2398,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | spl6_110)),
% 6.25/1.21    inference(resolution,[],[f2175,f1452])).
% 6.25/1.21  fof(f1452,plain,(
% 6.25/1.21    ( ! [X0,X1] : (v5_pre_topc(X1,sK0,X0) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0))))) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1451,f1419])).
% 6.25/1.21  fof(f1451,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1450,f1419])).
% 6.25/1.21  fof(f1450,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1449,f1419])).
% 6.25/1.21  fof(f1449,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1423,f1419])).
% 6.25/1.21  fof(f1423,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v1_funct_2(X1,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(backward_demodulation,[],[f475,f1419])).
% 6.25/1.21  fof(f475,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f474,f321])).
% 6.25/1.21  fof(f474,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f473,f321])).
% 6.25/1.21  fof(f473,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v1_funct_2(X1,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f472,f321])).
% 6.25/1.21  fof(f472,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f471,f321])).
% 6.25/1.21  fof(f471,plain,(
% 6.25/1.21    ( ! [X0,X1] : (~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(X1,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~v5_pre_topc(X1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X0) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f177,f321])).
% 6.25/1.21  fof(f2175,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_110),
% 6.25/1.21    inference(avatar_component_clause,[],[f2174])).
% 6.25/1.21  fof(f2174,plain,(
% 6.25/1.21    spl6_110 <=> v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.21    introduced(avatar_definition,[new_symbols(naming,[spl6_110])])).
% 6.25/1.21  fof(f2395,plain,(
% 6.25/1.21    ~spl6_110 | ~spl6_14 | spl6_51),
% 6.25/1.21    inference(avatar_split_clause,[],[f1942,f914,f269,f2174])).
% 6.25/1.21  fof(f1942,plain,(
% 6.25/1.21    ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | spl6_51)),
% 6.25/1.21    inference(forward_demodulation,[],[f916,f271])).
% 6.25/1.21  fof(f916,plain,(
% 6.25/1.21    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_51),
% 6.25/1.21    inference(avatar_component_clause,[],[f914])).
% 6.25/1.21  fof(f2394,plain,(
% 6.25/1.21    spl6_115 | ~spl6_14 | ~spl6_18 | spl6_74),
% 6.25/1.21    inference(avatar_split_clause,[],[f2381,f1542,f319,f269,f2333])).
% 6.25/1.21  fof(f2381,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_18 | spl6_74)),
% 6.25/1.21    inference(subsumption_resolution,[],[f1944,f1543])).
% 6.25/1.21  fof(f1944,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,sK0,sK1) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f1943,f271])).
% 6.25/1.21  fof(f1943,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | (~spl6_14 | ~spl6_18)),
% 6.25/1.21    inference(forward_demodulation,[],[f470,f271])).
% 6.25/1.21  fof(f470,plain,(
% 6.25/1.21    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | v5_pre_topc(sK2,sK0,sK1) | ~spl6_18),
% 6.25/1.21    inference(forward_demodulation,[],[f137,f321])).
% 6.25/1.21  fof(f2379,plain,(
% 6.25/1.21    ~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_77 | ~spl6_79 | ~spl6_110 | spl6_115),
% 6.25/1.21    inference(avatar_contradiction_clause,[],[f2378])).
% 6.25/1.21  fof(f2378,plain,(
% 6.25/1.21    $false | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_77 | ~spl6_79 | ~spl6_110 | spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2377,f1560])).
% 6.25/1.21  fof(f2377,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_79 | ~spl6_110 | spl6_115)),
% 6.25/1.21    inference(forward_demodulation,[],[f2376,f755])).
% 6.25/1.21  fof(f2376,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_79 | ~spl6_110 | spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2375,f1670])).
% 6.25/1.21  fof(f2375,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_38 | ~spl6_52 | ~spl6_53 | ~spl6_110 | spl6_115)),
% 6.25/1.21    inference(forward_demodulation,[],[f2374,f755])).
% 6.25/1.21  fof(f2374,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_52 | ~spl6_53 | ~spl6_110 | spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2373,f2176])).
% 6.25/1.21  fof(f2176,plain,(
% 6.25/1.21    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_110),
% 6.25/1.21    inference(avatar_component_clause,[],[f2174])).
% 6.25/1.21  fof(f2373,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_52 | ~spl6_53 | spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2372,f927])).
% 6.25/1.21  fof(f2372,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | ~spl6_53 | spl6_115)),
% 6.25/1.21    inference(subsumption_resolution,[],[f2371,f931])).
% 6.25/1.21  fof(f2371,plain,(
% 6.25/1.21    ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22 | spl6_115)),
% 6.25/1.21    inference(resolution,[],[f1790,f2335])).
% 6.25/1.22  fof(f2335,plain,(
% 6.25/1.22    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_115),
% 6.25/1.22    inference(avatar_component_clause,[],[f2333])).
% 6.25/1.22  fof(f1790,plain,(
% 6.25/1.22    ( ! [X0] : (v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1789,f73])).
% 6.25/1.22  fof(f1789,plain,(
% 6.25/1.22    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0)))) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1788,f73])).
% 6.25/1.22  fof(f1788,plain,(
% 6.25/1.22    ( ! [X0] : (~v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X0)))) | v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X0) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X0)))) | ~v5_pre_topc(k1_xboole_0,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18 | ~spl6_22)),
% 6.25/1.22    inference(resolution,[],[f1456,f581])).
% 6.25/1.22  fof(f1456,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k1_xboole_0),u1_struct_0(X2)))) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f1455,f1419])).
% 6.25/1.22  fof(f1455,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f1454,f1419])).
% 6.25/1.22  fof(f1454,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f1453,f1419])).
% 6.25/1.22  fof(f1453,plain,(
% 6.25/1.22    ( ! [X2,X3] : (v5_pre_topc(X3,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f1424,f1419])).
% 6.25/1.22  fof(f1424,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,k1_relat_1(k1_xboole_0),u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_14 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f480,f1419])).
% 6.25/1.22  fof(f480,plain,(
% 6.25/1.22    ( ! [X2,X3] : (v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f479,f321])).
% 6.25/1.22  fof(f479,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f478,f321])).
% 6.25/1.22  fof(f478,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f477,f321])).
% 6.25/1.22  fof(f477,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f476,f321])).
% 6.25/1.22  fof(f476,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X2)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X2)))) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)),X2) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f178,f321])).
% 6.25/1.22  fof(f2336,plain,(
% 6.25/1.22    ~spl6_115 | ~spl6_6 | ~spl6_14 | ~spl6_18 | spl6_31),
% 6.25/1.22    inference(avatar_split_clause,[],[f1490,f710,f319,f269,f182,f2333])).
% 6.25/1.22  fof(f182,plain,(
% 6.25/1.22    spl6_6 <=> sK2 = sK3),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 6.25/1.22  fof(f710,plain,(
% 6.25/1.22    spl6_31 <=> v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 6.25/1.22  fof(f1490,plain,(
% 6.25/1.22    ~v5_pre_topc(k1_xboole_0,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_6 | ~spl6_14 | ~spl6_18 | spl6_31)),
% 6.25/1.22    inference(backward_demodulation,[],[f1430,f1471])).
% 6.25/1.22  fof(f1471,plain,(
% 6.25/1.22    k1_xboole_0 = sK2 | (~spl6_6 | ~spl6_14)),
% 6.25/1.22    inference(backward_demodulation,[],[f184,f496])).
% 6.25/1.22  fof(f496,plain,(
% 6.25/1.22    k1_xboole_0 = sK3 | (~spl6_6 | ~spl6_14)),
% 6.25/1.22    inference(backward_demodulation,[],[f184,f271])).
% 6.25/1.22  fof(f184,plain,(
% 6.25/1.22    sK2 = sK3 | ~spl6_6),
% 6.25/1.22    inference(avatar_component_clause,[],[f182])).
% 6.25/1.22  fof(f1430,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_14 | ~spl6_18 | spl6_31)),
% 6.25/1.22    inference(backward_demodulation,[],[f712,f1419])).
% 6.25/1.22  fof(f712,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_31),
% 6.25/1.22    inference(avatar_component_clause,[],[f710])).
% 6.25/1.22  fof(f2321,plain,(
% 6.25/1.22    spl6_114 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_14),
% 6.25/1.22    inference(avatar_split_clause,[],[f2060,f269,f199,f194,f187,f2318])).
% 6.25/1.22  fof(f187,plain,(
% 6.25/1.22    spl6_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 6.25/1.22  fof(f194,plain,(
% 6.25/1.22    spl6_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 6.25/1.22  fof(f2060,plain,(
% 6.25/1.22    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),u1_struct_0(sK1)) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_14)),
% 6.25/1.22    inference(forward_demodulation,[],[f289,f271])).
% 6.25/1.22  fof(f289,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | (~spl6_7 | ~spl6_8 | ~spl6_9)),
% 6.25/1.22    inference(backward_demodulation,[],[f189,f280])).
% 6.25/1.22  fof(f280,plain,(
% 6.25/1.22    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl6_8 | ~spl6_9)),
% 6.25/1.22    inference(subsumption_resolution,[],[f278,f196])).
% 6.25/1.22  fof(f196,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_8),
% 6.25/1.22    inference(avatar_component_clause,[],[f194])).
% 6.25/1.22  fof(f278,plain,(
% 6.25/1.22    u1_struct_0(sK0) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_9),
% 6.25/1.22    inference(superposition,[],[f201,f107])).
% 6.25/1.22  fof(f201,plain,(
% 6.25/1.22    u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl6_9),
% 6.25/1.22    inference(avatar_component_clause,[],[f199])).
% 6.25/1.22  fof(f189,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_7),
% 6.25/1.22    inference(avatar_component_clause,[],[f187])).
% 6.25/1.22  fof(f2316,plain,(
% 6.25/1.22    ~spl6_78 | ~spl6_14 | spl6_15 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f2301,f319,f273,f269,f1661])).
% 6.25/1.22  fof(f273,plain,(
% 6.25/1.22    spl6_15 <=> k1_xboole_0 = u1_struct_0(sK0)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 6.25/1.22  fof(f2301,plain,(
% 6.25/1.22    k1_xboole_0 != k1_relat_1(k1_xboole_0) | (~spl6_14 | spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f452,f271])).
% 6.25/1.22  fof(f452,plain,(
% 6.25/1.22    k1_xboole_0 != k1_relat_1(sK2) | (spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(superposition,[],[f274,f321])).
% 6.25/1.22  fof(f274,plain,(
% 6.25/1.22    k1_xboole_0 != u1_struct_0(sK0) | spl6_15),
% 6.25/1.22    inference(avatar_component_clause,[],[f273])).
% 6.25/1.22  fof(f2310,plain,(
% 6.25/1.22    ~spl6_73 | ~spl6_14 | spl6_19),
% 6.25/1.22    inference(avatar_split_clause,[],[f2291,f396,f269,f1537])).
% 6.25/1.22  fof(f396,plain,(
% 6.25/1.22    spl6_19 <=> v1_funct_2(sK2,k1_xboole_0,k1_xboole_0)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 6.25/1.22  fof(f2291,plain,(
% 6.25/1.22    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl6_14 | spl6_19)),
% 6.25/1.22    inference(forward_demodulation,[],[f397,f271])).
% 6.25/1.22  fof(f397,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | spl6_19),
% 6.25/1.22    inference(avatar_component_clause,[],[f396])).
% 6.25/1.22  fof(f2276,plain,(
% 6.25/1.22    spl6_73 | ~spl6_83),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f2275])).
% 6.25/1.22  fof(f2275,plain,(
% 6.25/1.22    $false | (spl6_73 | ~spl6_83)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1539,f2210])).
% 6.25/1.22  fof(f2210,plain,(
% 6.25/1.22    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_83),
% 6.25/1.22    inference(subsumption_resolution,[],[f2112,f73])).
% 6.25/1.22  fof(f2112,plain,(
% 6.25/1.22    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_83),
% 6.25/1.22    inference(trivial_inequality_removal,[],[f2110])).
% 6.25/1.22  fof(f2110,plain,(
% 6.25/1.22    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_83),
% 6.25/1.22    inference(superposition,[],[f125,f1695])).
% 6.25/1.22  fof(f1695,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl6_83),
% 6.25/1.22    inference(avatar_component_clause,[],[f1694])).
% 6.25/1.22  fof(f1539,plain,(
% 6.25/1.22    ~v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | spl6_73),
% 6.25/1.22    inference(avatar_component_clause,[],[f1537])).
% 6.25/1.22  fof(f2177,plain,(
% 6.25/1.22    spl6_110 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_16 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38),
% 6.25/1.22    inference(avatar_split_clause,[],[f1575,f753,f706,f463,f319,f314,f308,f269,f241,f159,f154,f149,f144,f139,f2174])).
% 6.25/1.22  fof(f139,plain,(
% 6.25/1.22    spl6_1 <=> v1_funct_1(sK2)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 6.25/1.22  fof(f241,plain,(
% 6.25/1.22    spl6_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 6.25/1.22  fof(f308,plain,(
% 6.25/1.22    spl6_16 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 6.25/1.22  fof(f314,plain,(
% 6.25/1.22    spl6_17 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 6.25/1.22  fof(f463,plain,(
% 6.25/1.22    spl6_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 6.25/1.22  fof(f706,plain,(
% 6.25/1.22    spl6_30 <=> v5_pre_topc(sK2,sK0,sK1)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 6.25/1.22  fof(f1575,plain,(
% 6.25/1.22    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_16 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1572,f1574])).
% 6.25/1.22  fof(f1574,plain,(
% 6.25/1.22    v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_14 | ~spl6_16)),
% 6.25/1.22    inference(forward_demodulation,[],[f309,f271])).
% 6.25/1.22  fof(f309,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl6_16),
% 6.25/1.22    inference(avatar_component_clause,[],[f308])).
% 6.25/1.22  fof(f1572,plain,(
% 6.25/1.22    v5_pre_topc(k1_xboole_0,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1571,f271])).
% 6.25/1.22  fof(f1571,plain,(
% 6.25/1.22    ~v1_funct_2(k1_xboole_0,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1445,f271])).
% 6.25/1.22  fof(f1445,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(k1_xboole_0),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_14 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(backward_demodulation,[],[f1273,f1419])).
% 6.25/1.22  fof(f1273,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_11 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1272,f243])).
% 6.25/1.22  fof(f243,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl6_11),
% 6.25/1.22    inference(avatar_component_clause,[],[f241])).
% 6.25/1.22  fof(f1272,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1271,f122])).
% 6.25/1.22  fof(f122,plain,(
% 6.25/1.22    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 6.25/1.22    inference(equality_resolution,[],[f103])).
% 6.25/1.22  fof(f103,plain,(
% 6.25/1.22    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 6.25/1.22    inference(cnf_transformation,[],[f5])).
% 6.25/1.22  fof(f1271,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1270,f755])).
% 6.25/1.22  fof(f1270,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1269,f755])).
% 6.25/1.22  fof(f1269,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1268,f141])).
% 6.25/1.22  fof(f141,plain,(
% 6.25/1.22    v1_funct_1(sK2) | ~spl6_1),
% 6.25/1.22    inference(avatar_component_clause,[],[f139])).
% 6.25/1.22  fof(f1268,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1267,f151])).
% 6.25/1.22  fof(f1267,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1266,f146])).
% 6.25/1.22  fof(f1266,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1265,f316])).
% 6.25/1.22  fof(f316,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~spl6_17),
% 6.25/1.22    inference(avatar_component_clause,[],[f314])).
% 6.25/1.22  fof(f1265,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_21 | ~spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1005,f465])).
% 6.25/1.22  fof(f465,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~spl6_21),
% 6.25/1.22    inference(avatar_component_clause,[],[f463])).
% 6.25/1.22  fof(f1005,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_30)),
% 6.25/1.22    inference(resolution,[],[f707,f488])).
% 6.25/1.22  fof(f488,plain,(
% 6.25/1.22    ( ! [X6,X7] : (~v5_pre_topc(X7,sK0,X6) | ~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))))))) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f487,f321])).
% 6.25/1.22  fof(f487,plain,(
% 6.25/1.22    ( ! [X6,X7] : (~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~v5_pre_topc(X7,sK0,X6)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f486,f321])).
% 6.25/1.22  fof(f486,plain,(
% 6.25/1.22    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~v5_pre_topc(X7,sK0,X6)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f485,f321])).
% 6.25/1.22  fof(f485,plain,(
% 6.25/1.22    ( ! [X6,X7] : (~v1_funct_2(X7,k1_relat_1(sK2),u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6)))))) | v5_pre_topc(X7,sK0,g1_pre_topc(u1_struct_0(X6),u1_pre_topc(X6))) | ~v5_pre_topc(X7,sK0,X6)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f180,f321])).
% 6.25/1.22  fof(f707,plain,(
% 6.25/1.22    v5_pre_topc(sK2,sK0,sK1) | ~spl6_30),
% 6.25/1.22    inference(avatar_component_clause,[],[f706])).
% 6.25/1.22  fof(f1875,plain,(
% 6.25/1.22    ~spl6_74 | ~spl6_14 | spl6_30),
% 6.25/1.22    inference(avatar_split_clause,[],[f1873,f706,f269,f1542])).
% 6.25/1.22  fof(f1873,plain,(
% 6.25/1.22    ~v5_pre_topc(k1_xboole_0,sK0,sK1) | (~spl6_14 | spl6_30)),
% 6.25/1.22    inference(forward_demodulation,[],[f708,f271])).
% 6.25/1.22  fof(f708,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,sK0,sK1) | spl6_30),
% 6.25/1.22    inference(avatar_component_clause,[],[f706])).
% 6.25/1.22  fof(f1860,plain,(
% 6.25/1.22    k1_xboole_0 != u1_struct_0(sK1) | v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 6.25/1.22    introduced(theory_tautology_sat_conflict,[])).
% 6.25/1.22  fof(f1712,plain,(
% 6.25/1.22    spl6_85 | ~spl6_10 | ~spl6_53),
% 6.25/1.22    inference(avatar_split_clause,[],[f1592,f930,f203,f1709])).
% 6.25/1.22  fof(f1592,plain,(
% 6.25/1.22    v2_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | ~spl6_53)),
% 6.25/1.22    inference(backward_demodulation,[],[f931,f205])).
% 6.25/1.22  fof(f1704,plain,(
% 6.25/1.22    spl6_84 | ~spl6_10 | ~spl6_52),
% 6.25/1.22    inference(avatar_split_clause,[],[f1591,f926,f203,f1701])).
% 6.25/1.22  fof(f1591,plain,(
% 6.25/1.22    l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | ~spl6_52)),
% 6.25/1.22    inference(backward_demodulation,[],[f927,f205])).
% 6.25/1.22  fof(f1699,plain,(
% 6.25/1.22    spl6_45 | ~spl6_10 | ~spl6_38),
% 6.25/1.22    inference(avatar_split_clause,[],[f1590,f753,f203,f845])).
% 6.25/1.22  fof(f1590,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | (~spl6_10 | ~spl6_38)),
% 6.25/1.22    inference(backward_demodulation,[],[f755,f205])).
% 6.25/1.22  fof(f1678,plain,(
% 6.25/1.22    spl6_80 | ~spl6_14 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f499,f319,f269,f1675])).
% 6.25/1.22  fof(f1671,plain,(
% 6.25/1.22    spl6_79 | ~spl6_6 | ~spl6_14 | ~spl6_18 | ~spl6_63),
% 6.25/1.22    inference(avatar_split_clause,[],[f1495,f1308,f319,f269,f182,f1668])).
% 6.25/1.22  fof(f1308,plain,(
% 6.25/1.22    spl6_63 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 6.25/1.22  fof(f1495,plain,(
% 6.25/1.22    v1_funct_2(k1_xboole_0,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_6 | ~spl6_14 | ~spl6_18 | ~spl6_63)),
% 6.25/1.22    inference(backward_demodulation,[],[f1446,f1471])).
% 6.25/1.22  fof(f1446,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(k1_xboole_0),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_14 | ~spl6_18 | ~spl6_63)),
% 6.25/1.22    inference(backward_demodulation,[],[f1310,f1419])).
% 6.25/1.22  fof(f1310,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | ~spl6_63),
% 6.25/1.22    inference(avatar_component_clause,[],[f1308])).
% 6.25/1.22  fof(f1659,plain,(
% 6.25/1.22    spl6_77 | ~spl6_14 | ~spl6_16),
% 6.25/1.22    inference(avatar_split_clause,[],[f1574,f308,f269,f1559])).
% 6.25/1.22  fof(f1333,plain,(
% 6.25/1.22    ~spl6_11 | spl6_14 | spl6_19 | ~spl6_63),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f1332])).
% 6.25/1.22  fof(f1332,plain,(
% 6.25/1.22    $false | (~spl6_11 | spl6_14 | spl6_19 | ~spl6_63)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1322,f397])).
% 6.25/1.22  fof(f1322,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_11 | spl6_14 | ~spl6_63)),
% 6.25/1.22    inference(backward_demodulation,[],[f1310,f1316])).
% 6.25/1.22  fof(f1316,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_11 | spl6_14 | ~spl6_63)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1315,f243])).
% 6.25/1.22  fof(f1315,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (spl6_14 | ~spl6_63)),
% 6.25/1.22    inference(forward_demodulation,[],[f1314,f122])).
% 6.25/1.22  fof(f1314,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (spl6_14 | ~spl6_63)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1312,f270])).
% 6.25/1.22  fof(f270,plain,(
% 6.25/1.22    k1_xboole_0 != sK2 | spl6_14),
% 6.25/1.22    inference(avatar_component_clause,[],[f269])).
% 6.25/1.22  fof(f1312,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | ~spl6_63),
% 6.25/1.22    inference(resolution,[],[f1310,f126])).
% 6.25/1.22  fof(f126,plain,(
% 6.25/1.22    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 6.25/1.22    inference(equality_resolution,[],[f111])).
% 6.25/1.22  fof(f111,plain,(
% 6.25/1.22    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 6.25/1.22    inference(cnf_transformation,[],[f55])).
% 6.25/1.22  fof(f1311,plain,(
% 6.25/1.22    spl6_63 | ~spl6_27 | ~spl6_38),
% 6.25/1.22    inference(avatar_split_clause,[],[f1191,f753,f689,f1308])).
% 6.25/1.22  fof(f689,plain,(
% 6.25/1.22    spl6_27 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 6.25/1.22  fof(f1191,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_27 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f691,f755])).
% 6.25/1.22  fof(f691,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_27),
% 6.25/1.22    inference(avatar_component_clause,[],[f689])).
% 6.25/1.22  fof(f1303,plain,(
% 6.25/1.22    ~spl6_11 | ~spl6_34 | spl6_62),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f1302])).
% 6.25/1.22  fof(f1302,plain,(
% 6.25/1.22    $false | (~spl6_11 | ~spl6_34 | spl6_62)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1301,f243])).
% 6.25/1.22  fof(f1301,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_34 | spl6_62)),
% 6.25/1.22    inference(forward_demodulation,[],[f1300,f122])).
% 6.25/1.22  fof(f1300,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (~spl6_34 | spl6_62)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1294,f1279])).
% 6.25/1.22  fof(f1279,plain,(
% 6.25/1.22    k1_xboole_0 != k1_relat_1(sK2) | spl6_62),
% 6.25/1.22    inference(avatar_component_clause,[],[f1277])).
% 6.25/1.22  fof(f1277,plain,(
% 6.25/1.22    spl6_62 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 6.25/1.22  fof(f1294,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_34),
% 6.25/1.22    inference(superposition,[],[f107,f730])).
% 6.25/1.22  fof(f730,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl6_34),
% 6.25/1.22    inference(avatar_component_clause,[],[f728])).
% 6.25/1.22  fof(f728,plain,(
% 6.25/1.22    spl6_34 <=> k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 6.25/1.22  fof(f1280,plain,(
% 6.25/1.22    ~spl6_62 | spl6_15 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f452,f319,f273,f1277])).
% 6.25/1.22  fof(f1262,plain,(
% 6.25/1.22    ~spl6_11 | spl6_14 | ~spl6_15 | ~spl6_18 | ~spl6_34 | spl6_37 | ~spl6_38 | ~spl6_60),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f1261])).
% 6.25/1.22  fof(f1261,plain,(
% 6.25/1.22    $false | (~spl6_11 | spl6_14 | ~spl6_15 | ~spl6_18 | ~spl6_34 | spl6_37 | ~spl6_38 | ~spl6_60)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1245,f730])).
% 6.25/1.22  fof(f1245,plain,(
% 6.25/1.22    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (~spl6_11 | spl6_14 | ~spl6_15 | ~spl6_18 | spl6_37 | ~spl6_38 | ~spl6_60)),
% 6.25/1.22    inference(backward_demodulation,[],[f1212,f1240])).
% 6.25/1.22  fof(f1240,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (~spl6_11 | spl6_14 | ~spl6_60)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1239,f243])).
% 6.25/1.22  fof(f1239,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | (spl6_14 | ~spl6_60)),
% 6.25/1.22    inference(forward_demodulation,[],[f1238,f122])).
% 6.25/1.22  fof(f1238,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | (spl6_14 | ~spl6_60)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1236,f270])).
% 6.25/1.22  fof(f1236,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0))) | ~spl6_60),
% 6.25/1.22    inference(resolution,[],[f1229,f126])).
% 6.25/1.22  fof(f1229,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | ~spl6_60),
% 6.25/1.22    inference(avatar_component_clause,[],[f1227])).
% 6.25/1.22  fof(f1227,plain,(
% 6.25/1.22    spl6_60 <=> v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 6.25/1.22  fof(f1212,plain,(
% 6.25/1.22    u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0,sK2) | (~spl6_15 | ~spl6_18 | spl6_37 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f1211,f1079])).
% 6.25/1.22  fof(f1079,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relat_1(sK2) | (~spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f321,f595])).
% 6.25/1.22  fof(f595,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK0) | (~spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f321,f400])).
% 6.25/1.22  fof(f400,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relat_1(sK2) | (~spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f321,f275])).
% 6.25/1.22  fof(f275,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK0) | ~spl6_15),
% 6.25/1.22    inference(avatar_component_clause,[],[f273])).
% 6.25/1.22  fof(f1211,plain,(
% 6.25/1.22    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0,sK2) | (spl6_37 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f750,f755])).
% 6.25/1.22  fof(f750,plain,(
% 6.25/1.22    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) != k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | spl6_37),
% 6.25/1.22    inference(avatar_component_clause,[],[f749])).
% 6.25/1.22  fof(f749,plain,(
% 6.25/1.22    spl6_37 <=> u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2)),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 6.25/1.22  fof(f1230,plain,(
% 6.25/1.22    spl6_60 | ~spl6_15 | ~spl6_18 | ~spl6_27 | ~spl6_38),
% 6.25/1.22    inference(avatar_split_clause,[],[f1178,f753,f689,f319,f273,f1227])).
% 6.25/1.22  fof(f1178,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_15 | ~spl6_18 | ~spl6_27 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f759,f1079])).
% 6.25/1.22  fof(f759,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0) | (~spl6_27 | ~spl6_38)),
% 6.25/1.22    inference(backward_demodulation,[],[f691,f755])).
% 6.25/1.22  fof(f1225,plain,(
% 6.25/1.22    spl6_11 | ~spl6_8 | ~spl6_15),
% 6.25/1.22    inference(avatar_split_clause,[],[f358,f273,f194,f241])).
% 6.25/1.22  fof(f358,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_15)),
% 6.25/1.22    inference(forward_demodulation,[],[f334,f123])).
% 6.25/1.22  fof(f334,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(sK1)))) | (~spl6_8 | ~spl6_15)),
% 6.25/1.22    inference(backward_demodulation,[],[f196,f275])).
% 6.25/1.22  fof(f1020,plain,(
% 6.25/1.22    ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_29 | ~spl6_30 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | ~spl6_52 | ~spl6_53),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f1019])).
% 6.25/1.22  fof(f1019,plain,(
% 6.25/1.22    $false | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_29 | ~spl6_30 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | ~spl6_52 | ~spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1018,f1012])).
% 6.25/1.22  fof(f1012,plain,(
% 6.25/1.22    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41 | ~spl6_42)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1011,f831])).
% 6.25/1.22  fof(f831,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_42),
% 6.25/1.22    inference(avatar_component_clause,[],[f829])).
% 6.25/1.22  fof(f829,plain,(
% 6.25/1.22    spl6_42 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).
% 6.25/1.22  fof(f1011,plain,(
% 6.25/1.22    v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1010,f141])).
% 6.25/1.22  fof(f1010,plain,(
% 6.25/1.22    ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1009,f151])).
% 6.25/1.22  fof(f1009,plain,(
% 6.25/1.22    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1008,f146])).
% 6.25/1.22  fof(f1008,plain,(
% 6.25/1.22    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1007,f316])).
% 6.25/1.22  fof(f1007,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_21 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1006,f465])).
% 6.25/1.22  fof(f1006,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_30 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1005,f820])).
% 6.25/1.22  fof(f820,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_41),
% 6.25/1.22    inference(avatar_component_clause,[],[f818])).
% 6.25/1.22  fof(f818,plain,(
% 6.25/1.22    spl6_41 <=> v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 6.25/1.22  fof(f1018,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | ~spl6_52 | ~spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1017,f141])).
% 6.25/1.22  fof(f1017,plain,(
% 6.25/1.22    ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | ~spl6_52 | ~spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1016,f927])).
% 6.25/1.22  fof(f1016,plain,(
% 6.25/1.22    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | ~spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1015,f931])).
% 6.25/1.22  fof(f1015,plain,(
% 6.25/1.22    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1014,f831])).
% 6.25/1.22  fof(f1014,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37 | ~spl6_41)),
% 6.25/1.22    inference(subsumption_resolution,[],[f1013,f820])).
% 6.25/1.22  fof(f1013,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | spl6_31 | ~spl6_37)),
% 6.25/1.22    inference(resolution,[],[f712,f797])).
% 6.25/1.22  fof(f797,plain,(
% 6.25/1.22    ( ! [X2,X3] : (v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(duplicate_literal_removal,[],[f796])).
% 6.25/1.22  fof(f796,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(forward_demodulation,[],[f792,f782])).
% 6.25/1.22  fof(f782,plain,(
% 6.25/1.22    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | (~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(subsumption_resolution,[],[f780,f703])).
% 6.25/1.22  fof(f703,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_29),
% 6.25/1.22    inference(avatar_component_clause,[],[f701])).
% 6.25/1.22  fof(f701,plain,(
% 6.25/1.22    spl6_29 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 6.25/1.22  fof(f780,plain,(
% 6.25/1.22    k1_relat_1(sK2) = u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_37),
% 6.25/1.22    inference(superposition,[],[f751,f107])).
% 6.25/1.22  fof(f751,plain,(
% 6.25/1.22    u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~spl6_37),
% 6.25/1.22    inference(avatar_component_clause,[],[f749])).
% 6.25/1.22  fof(f792,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(duplicate_literal_removal,[],[f784])).
% 6.25/1.22  fof(f784,plain,(
% 6.25/1.22    ( ! [X2,X3] : (~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | v5_pre_topc(X3,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X2)))) | ~v1_funct_2(X3,k1_relat_1(sK2),u1_struct_0(X2)) | ~v2_pre_topc(X2) | ~l1_pre_topc(X2) | ~v1_funct_1(X3) | ~v5_pre_topc(X3,sK0,X2)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(backward_demodulation,[],[f480,f782])).
% 6.25/1.22  fof(f984,plain,(
% 6.25/1.22    ~spl6_2 | ~spl6_3 | spl6_53),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f983])).
% 6.25/1.22  fof(f983,plain,(
% 6.25/1.22    $false | (~spl6_2 | ~spl6_3 | spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f982,f146])).
% 6.25/1.22  fof(f982,plain,(
% 6.25/1.22    ~v2_pre_topc(sK1) | (~spl6_3 | spl6_53)),
% 6.25/1.22    inference(subsumption_resolution,[],[f981,f151])).
% 6.25/1.22  fof(f981,plain,(
% 6.25/1.22    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl6_53),
% 6.25/1.22    inference(resolution,[],[f932,f77])).
% 6.25/1.22  fof(f932,plain,(
% 6.25/1.22    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_53),
% 6.25/1.22    inference(avatar_component_clause,[],[f930])).
% 6.25/1.22  fof(f963,plain,(
% 6.25/1.22    ~spl6_3 | spl6_57),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f962])).
% 6.25/1.22  fof(f962,plain,(
% 6.25/1.22    $false | (~spl6_3 | spl6_57)),
% 6.25/1.22    inference(subsumption_resolution,[],[f958,f151])).
% 6.25/1.22  fof(f958,plain,(
% 6.25/1.22    ~l1_pre_topc(sK1) | spl6_57),
% 6.25/1.22    inference(resolution,[],[f952,f75])).
% 6.25/1.22  fof(f952,plain,(
% 6.25/1.22    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl6_57),
% 6.25/1.22    inference(avatar_component_clause,[],[f950])).
% 6.25/1.22  fof(f950,plain,(
% 6.25/1.22    spl6_57 <=> m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 6.25/1.22  fof(f953,plain,(
% 6.25/1.22    ~spl6_57 | spl6_52),
% 6.25/1.22    inference(avatar_split_clause,[],[f939,f926,f950])).
% 6.25/1.22  fof(f939,plain,(
% 6.25/1.22    ~m1_subset_1(u1_pre_topc(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK1)))) | spl6_52),
% 6.25/1.22    inference(resolution,[],[f928,f93])).
% 6.25/1.22  fof(f928,plain,(
% 6.25/1.22    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl6_52),
% 6.25/1.22    inference(avatar_component_clause,[],[f926])).
% 6.25/1.22  fof(f933,plain,(
% 6.25/1.22    ~spl6_52 | ~spl6_53 | ~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | spl6_51),
% 6.25/1.22    inference(avatar_split_clause,[],[f924,f914,f829,f818,f749,f710,f701,f319,f159,f154,f139,f930,f926])).
% 6.25/1.22  fof(f924,plain,(
% 6.25/1.22    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_31 | ~spl6_37 | ~spl6_41 | ~spl6_42 | spl6_51)),
% 6.25/1.22    inference(subsumption_resolution,[],[f923,f820])).
% 6.25/1.22  fof(f923,plain,(
% 6.25/1.22    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_31 | ~spl6_37 | ~spl6_42 | spl6_51)),
% 6.25/1.22    inference(subsumption_resolution,[],[f922,f831])).
% 6.25/1.22  fof(f922,plain,(
% 6.25/1.22    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_31 | ~spl6_37 | spl6_51)),
% 6.25/1.22    inference(subsumption_resolution,[],[f919,f711])).
% 6.25/1.22  fof(f711,plain,(
% 6.25/1.22    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl6_31),
% 6.25/1.22    inference(avatar_component_clause,[],[f710])).
% 6.25/1.22  fof(f919,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37 | spl6_51)),
% 6.25/1.22    inference(resolution,[],[f916,f853])).
% 6.25/1.22  fof(f853,plain,(
% 6.25/1.22    ( ! [X0] : (v5_pre_topc(sK2,sK0,X0) | ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))) ) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(resolution,[],[f795,f141])).
% 6.25/1.22  fof(f795,plain,(
% 6.25/1.22    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(duplicate_literal_removal,[],[f794])).
% 6.25/1.22  fof(f794,plain,(
% 6.25/1.22    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(forward_demodulation,[],[f793,f782])).
% 6.25/1.22  fof(f793,plain,(
% 6.25/1.22    ( ! [X0,X1] : (~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(duplicate_literal_removal,[],[f783])).
% 6.25/1.22  fof(f783,plain,(
% 6.25/1.22    ( ! [X0,X1] : (~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v5_pre_topc(X1,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(X1,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | v5_pre_topc(X1,sK0,X0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(backward_demodulation,[],[f475,f782])).
% 6.25/1.22  fof(f917,plain,(
% 6.25/1.22    ~spl6_51 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30 | ~spl6_41 | ~spl6_42),
% 6.25/1.22    inference(avatar_split_clause,[],[f911,f829,f818,f706,f463,f319,f314,f159,f154,f149,f144,f139,f914])).
% 6.25/1.22  fof(f911,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30 | ~spl6_41 | ~spl6_42)),
% 6.25/1.22    inference(subsumption_resolution,[],[f910,f820])).
% 6.25/1.22  fof(f910,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30 | ~spl6_42)),
% 6.25/1.22    inference(subsumption_resolution,[],[f909,f831])).
% 6.25/1.22  fof(f909,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f908,f151])).
% 6.25/1.22  fof(f908,plain,(
% 6.25/1.22    ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f907,f146])).
% 6.25/1.22  fof(f907,plain,(
% 6.25/1.22    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_17 | ~spl6_18 | ~spl6_21 | spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f906,f316])).
% 6.25/1.22  fof(f906,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | ~spl6_21 | spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f903,f465])).
% 6.25/1.22  fof(f903,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18 | spl6_30)),
% 6.25/1.22    inference(resolution,[],[f868,f708])).
% 6.25/1.22  fof(f868,plain,(
% 6.25/1.22    ( ! [X0] : (v5_pre_topc(sK2,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v5_pre_topc(sK2,sK0,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) ) | (~spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_18)),
% 6.25/1.22    inference(resolution,[],[f484,f141])).
% 6.25/1.22  fof(f858,plain,(
% 6.25/1.22    ~spl6_46 | spl6_44),
% 6.25/1.22    inference(avatar_split_clause,[],[f849,f841,f855])).
% 6.25/1.22  fof(f841,plain,(
% 6.25/1.22    spl6_44 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).
% 6.25/1.22  fof(f849,plain,(
% 6.25/1.22    ~r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))))) | spl6_44),
% 6.25/1.22    inference(resolution,[],[f843,f99])).
% 6.25/1.22  fof(f99,plain,(
% 6.25/1.22    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.25/1.22    inference(cnf_transformation,[],[f10])).
% 6.25/1.22  fof(f10,axiom,(
% 6.25/1.22    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.25/1.22    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.25/1.22  fof(f843,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | spl6_44),
% 6.25/1.22    inference(avatar_component_clause,[],[f841])).
% 6.25/1.22  fof(f848,plain,(
% 6.25/1.22    ~spl6_44 | spl6_45 | spl6_39),
% 6.25/1.22    inference(avatar_split_clause,[],[f811,f802,f845,f841])).
% 6.25/1.22  fof(f811,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | spl6_39),
% 6.25/1.22    inference(subsumption_resolution,[],[f810,f107])).
% 6.25/1.22  fof(f810,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))) | k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1))),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))))) | spl6_39),
% 6.25/1.22    inference(resolution,[],[f803,f114])).
% 6.25/1.22  fof(f114,plain,(
% 6.25/1.22    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.25/1.22    inference(cnf_transformation,[],[f55])).
% 6.25/1.22  fof(f803,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | spl6_39),
% 6.25/1.22    inference(avatar_component_clause,[],[f802])).
% 6.25/1.22  fof(f832,plain,(
% 6.25/1.22    spl6_42 | ~spl6_29 | ~spl6_37),
% 6.25/1.22    inference(avatar_split_clause,[],[f788,f749,f701,f829])).
% 6.25/1.22  fof(f788,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | (~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(backward_demodulation,[],[f703,f782])).
% 6.25/1.22  fof(f821,plain,(
% 6.25/1.22    spl6_41 | ~spl6_27 | ~spl6_29 | ~spl6_37),
% 6.25/1.22    inference(avatar_split_clause,[],[f787,f749,f701,f689,f818])).
% 6.25/1.22  fof(f787,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (~spl6_27 | ~spl6_29 | ~spl6_37)),
% 6.25/1.22    inference(backward_demodulation,[],[f691,f782])).
% 6.25/1.22  fof(f768,plain,(
% 6.25/1.22    spl6_11 | ~spl6_29 | ~spl6_38),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f767])).
% 6.25/1.22  fof(f767,plain,(
% 6.25/1.22    $false | (spl6_11 | ~spl6_29 | ~spl6_38)),
% 6.25/1.22    inference(subsumption_resolution,[],[f766,f242])).
% 6.25/1.22  fof(f242,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | spl6_11),
% 6.25/1.22    inference(avatar_component_clause,[],[f241])).
% 6.25/1.22  fof(f766,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_29 | ~spl6_38)),
% 6.25/1.22    inference(forward_demodulation,[],[f760,f122])).
% 6.25/1.22  fof(f760,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),k1_xboole_0))) | (~spl6_29 | ~spl6_38)),
% 6.25/1.22    inference(backward_demodulation,[],[f703,f755])).
% 6.25/1.22  fof(f756,plain,(
% 6.25/1.22    spl6_37 | spl6_38 | ~spl6_18 | ~spl6_27),
% 6.25/1.22    inference(avatar_split_clause,[],[f699,f689,f319,f753,f749])).
% 6.25/1.22  fof(f699,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | (~spl6_18 | ~spl6_27)),
% 6.25/1.22    inference(subsumption_resolution,[],[f698,f467])).
% 6.25/1.22  fof(f467,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_18),
% 6.25/1.22    inference(forward_demodulation,[],[f133,f321])).
% 6.25/1.22  fof(f133,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.25/1.22    inference(forward_demodulation,[],[f62,f63])).
% 6.25/1.22  fof(f62,plain,(
% 6.25/1.22    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))))),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f698,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))) = k1_relset_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))))) | ~spl6_27),
% 6.25/1.22    inference(resolution,[],[f691,f115])).
% 6.25/1.22  fof(f731,plain,(
% 6.25/1.22    spl6_34 | ~spl6_11 | ~spl6_19),
% 6.25/1.22    inference(avatar_split_clause,[],[f643,f396,f241,f728])).
% 6.25/1.22  fof(f643,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~spl6_19),
% 6.25/1.22    inference(forward_demodulation,[],[f636,f122])).
% 6.25/1.22  fof(f636,plain,(
% 6.25/1.22    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~spl6_19),
% 6.25/1.22    inference(resolution,[],[f398,f124])).
% 6.25/1.22  fof(f124,plain,(
% 6.25/1.22    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 6.25/1.22    inference(equality_resolution,[],[f113])).
% 6.25/1.22  fof(f113,plain,(
% 6.25/1.22    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 6.25/1.22    inference(cnf_transformation,[],[f55])).
% 6.25/1.22  fof(f398,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | ~spl6_19),
% 6.25/1.22    inference(avatar_component_clause,[],[f396])).
% 6.25/1.22  fof(f715,plain,(
% 6.25/1.22    spl6_31 | ~spl6_18 | spl6_30),
% 6.25/1.22    inference(avatar_split_clause,[],[f714,f706,f319,f710])).
% 6.25/1.22  fof(f714,plain,(
% 6.25/1.22    v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl6_18 | spl6_30)),
% 6.25/1.22    inference(subsumption_resolution,[],[f470,f708])).
% 6.25/1.22  fof(f713,plain,(
% 6.25/1.22    ~spl6_30 | ~spl6_31 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f469,f319,f710,f706])).
% 6.25/1.22  fof(f469,plain,(
% 6.25/1.22    ~v5_pre_topc(sK2,g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0)),g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v5_pre_topc(sK2,sK0,sK1) | ~spl6_18),
% 6.25/1.22    inference(forward_demodulation,[],[f136,f321])).
% 6.25/1.22  fof(f704,plain,(
% 6.25/1.22    spl6_29 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f467,f319,f701])).
% 6.25/1.22  fof(f692,plain,(
% 6.25/1.22    spl6_27 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f468,f319,f689])).
% 6.25/1.22  fof(f468,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(k1_relat_1(sK2),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl6_18),
% 6.25/1.22    inference(forward_demodulation,[],[f134,f321])).
% 6.25/1.22  fof(f134,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.25/1.22    inference(forward_demodulation,[],[f61,f63])).
% 6.25/1.22  fof(f61,plain,(
% 6.25/1.22    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f672,plain,(
% 6.25/1.22    spl6_21 | ~spl6_8 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f490,f319,f194,f463])).
% 6.25/1.22  fof(f490,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl6_8 | ~spl6_18)),
% 6.25/1.22    inference(forward_demodulation,[],[f196,f321])).
% 6.25/1.22  fof(f642,plain,(
% 6.25/1.22    spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_15 | ~spl6_18 | ~spl6_19),
% 6.25/1.22    inference(avatar_contradiction_clause,[],[f641])).
% 6.25/1.22  fof(f641,plain,(
% 6.25/1.22    $false | (spl6_9 | ~spl6_10 | ~spl6_11 | ~spl6_15 | ~spl6_18 | ~spl6_19)),
% 6.25/1.22    inference(subsumption_resolution,[],[f640,f243])).
% 6.25/1.22  fof(f640,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (spl6_9 | ~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_19)),
% 6.25/1.22    inference(forward_demodulation,[],[f639,f122])).
% 6.25/1.22  fof(f639,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | (spl6_9 | ~spl6_10 | ~spl6_15 | ~spl6_18 | ~spl6_19)),
% 6.25/1.22    inference(subsumption_resolution,[],[f636,f608])).
% 6.25/1.22  fof(f608,plain,(
% 6.25/1.22    k1_xboole_0 != k1_relset_1(k1_xboole_0,k1_xboole_0,sK2) | (spl6_9 | ~spl6_10 | ~spl6_15 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f591,f400])).
% 6.25/1.22  fof(f591,plain,(
% 6.25/1.22    k1_relat_1(sK2) != k1_relset_1(k1_relat_1(sK2),k1_xboole_0,sK2) | (spl6_9 | ~spl6_10 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f583,f321])).
% 6.25/1.22  fof(f635,plain,(
% 6.25/1.22    spl6_19 | ~spl6_10 | ~spl6_20),
% 6.25/1.22    inference(avatar_split_clause,[],[f593,f415,f203,f396])).
% 6.25/1.22  fof(f415,plain,(
% 6.25/1.22    spl6_20 <=> v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1))),
% 6.25/1.22    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 6.25/1.22  fof(f593,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_10 | ~spl6_20)),
% 6.25/1.22    inference(forward_demodulation,[],[f417,f205])).
% 6.25/1.22  fof(f417,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | ~spl6_20),
% 6.25/1.22    inference(avatar_component_clause,[],[f415])).
% 6.25/1.22  fof(f634,plain,(
% 6.25/1.22    spl6_11 | ~spl6_8 | ~spl6_10),
% 6.25/1.22    inference(avatar_split_clause,[],[f239,f203,f194,f241])).
% 6.25/1.22  fof(f239,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl6_8 | ~spl6_10)),
% 6.25/1.22    inference(forward_demodulation,[],[f216,f122])).
% 6.25/1.22  fof(f216,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | (~spl6_8 | ~spl6_10)),
% 6.25/1.22    inference(backward_demodulation,[],[f196,f205])).
% 6.25/1.22  fof(f582,plain,(
% 6.25/1.22    spl6_22 | ~spl6_1 | ~spl6_14),
% 6.25/1.22    inference(avatar_split_clause,[],[f493,f269,f139,f579])).
% 6.25/1.22  fof(f493,plain,(
% 6.25/1.22    v1_funct_1(k1_xboole_0) | (~spl6_1 | ~spl6_14)),
% 6.25/1.22    inference(backward_demodulation,[],[f141,f271])).
% 6.25/1.22  fof(f466,plain,(
% 6.25/1.22    spl6_21 | ~spl6_8 | ~spl6_9),
% 6.25/1.22    inference(avatar_split_clause,[],[f290,f199,f194,f463])).
% 6.25/1.22  fof(f290,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | (~spl6_8 | ~spl6_9)),
% 6.25/1.22    inference(backward_demodulation,[],[f196,f280])).
% 6.25/1.22  fof(f451,plain,(
% 6.25/1.22    spl6_17 | ~spl6_7 | ~spl6_8 | ~spl6_9),
% 6.25/1.22    inference(avatar_split_clause,[],[f289,f199,f194,f187,f314])).
% 6.25/1.22  fof(f450,plain,(
% 6.25/1.22    spl6_18 | ~spl6_8 | ~spl6_9),
% 6.25/1.22    inference(avatar_split_clause,[],[f280,f199,f194,f319])).
% 6.25/1.22  fof(f418,plain,(
% 6.25/1.22    spl6_20 | ~spl6_7 | ~spl6_15),
% 6.25/1.22    inference(avatar_split_clause,[],[f333,f273,f187,f415])).
% 6.25/1.22  fof(f333,plain,(
% 6.25/1.22    v1_funct_2(sK2,k1_xboole_0,u1_struct_0(sK1)) | (~spl6_7 | ~spl6_15)),
% 6.25/1.22    inference(backward_demodulation,[],[f189,f275])).
% 6.25/1.22  fof(f412,plain,(
% 6.25/1.22    ~spl6_19 | ~spl6_15 | spl6_16 | ~spl6_18),
% 6.25/1.22    inference(avatar_split_clause,[],[f401,f319,f308,f273,f396])).
% 6.25/1.22  fof(f401,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_xboole_0,k1_xboole_0) | (~spl6_15 | spl6_16 | ~spl6_18)),
% 6.25/1.22    inference(backward_demodulation,[],[f310,f400])).
% 6.25/1.22  fof(f310,plain,(
% 6.25/1.22    ~v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | spl6_16),
% 6.25/1.22    inference(avatar_component_clause,[],[f308])).
% 6.25/1.22  fof(f276,plain,(
% 6.25/1.22    spl6_14 | spl6_15 | ~spl6_11 | ~spl6_12),
% 6.25/1.22    inference(avatar_split_clause,[],[f261,f254,f241,f273,f269])).
% 6.25/1.22  fof(f261,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | (~spl6_11 | ~spl6_12)),
% 6.25/1.22    inference(subsumption_resolution,[],[f260,f243])).
% 6.25/1.22  fof(f260,plain,(
% 6.25/1.22    ~m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | ~spl6_12),
% 6.25/1.22    inference(forward_demodulation,[],[f258,f122])).
% 6.25/1.22  fof(f258,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~spl6_12),
% 6.25/1.22    inference(resolution,[],[f256,f126])).
% 6.25/1.22  fof(f266,plain,(
% 6.25/1.22    spl6_13 | ~spl6_10),
% 6.25/1.22    inference(avatar_split_clause,[],[f208,f203,f263])).
% 6.25/1.22  fof(f208,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK1)))) | ~spl6_10),
% 6.25/1.22    inference(backward_demodulation,[],[f134,f205])).
% 6.25/1.22  fof(f257,plain,(
% 6.25/1.22    spl6_12 | ~spl6_7 | ~spl6_10),
% 6.25/1.22    inference(avatar_split_clause,[],[f215,f203,f187,f254])).
% 6.25/1.22  fof(f215,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(sK0),k1_xboole_0) | (~spl6_7 | ~spl6_10)),
% 6.25/1.22    inference(backward_demodulation,[],[f189,f205])).
% 6.25/1.22  fof(f206,plain,(
% 6.25/1.22    spl6_9 | spl6_10 | ~spl6_7),
% 6.25/1.22    inference(avatar_split_clause,[],[f192,f187,f203,f199])).
% 6.25/1.22  fof(f192,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl6_7),
% 6.25/1.22    inference(subsumption_resolution,[],[f191,f66])).
% 6.25/1.22  fof(f66,plain,(
% 6.25/1.22    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f191,plain,(
% 6.25/1.22    k1_xboole_0 = u1_struct_0(sK1) | u1_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_7),
% 6.25/1.22    inference(resolution,[],[f189,f115])).
% 6.25/1.22  fof(f197,plain,(
% 6.25/1.22    spl6_8),
% 6.25/1.22    inference(avatar_split_clause,[],[f66,f194])).
% 6.25/1.22  fof(f190,plain,(
% 6.25/1.22    spl6_7),
% 6.25/1.22    inference(avatar_split_clause,[],[f65,f187])).
% 6.25/1.22  fof(f65,plain,(
% 6.25/1.22    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f185,plain,(
% 6.25/1.22    spl6_6),
% 6.25/1.22    inference(avatar_split_clause,[],[f63,f182])).
% 6.25/1.22  fof(f162,plain,(
% 6.25/1.22    spl6_5),
% 6.25/1.22    inference(avatar_split_clause,[],[f70,f159])).
% 6.25/1.22  fof(f70,plain,(
% 6.25/1.22    l1_pre_topc(sK0)),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f157,plain,(
% 6.25/1.22    spl6_4),
% 6.25/1.22    inference(avatar_split_clause,[],[f69,f154])).
% 6.25/1.22  fof(f69,plain,(
% 6.25/1.22    v2_pre_topc(sK0)),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f152,plain,(
% 6.25/1.22    spl6_3),
% 6.25/1.22    inference(avatar_split_clause,[],[f68,f149])).
% 6.25/1.22  fof(f68,plain,(
% 6.25/1.22    l1_pre_topc(sK1)),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f147,plain,(
% 6.25/1.22    spl6_2),
% 6.25/1.22    inference(avatar_split_clause,[],[f67,f144])).
% 6.25/1.22  fof(f67,plain,(
% 6.25/1.22    v2_pre_topc(sK1)),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  fof(f142,plain,(
% 6.25/1.22    spl6_1),
% 6.25/1.22    inference(avatar_split_clause,[],[f64,f139])).
% 6.25/1.22  fof(f64,plain,(
% 6.25/1.22    v1_funct_1(sK2)),
% 6.25/1.22    inference(cnf_transformation,[],[f30])).
% 6.25/1.22  % SZS output end Proof for theBenchmark
% 6.25/1.22  % (18220)------------------------------
% 6.25/1.22  % (18220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.25/1.22  % (18220)Termination reason: Refutation
% 6.25/1.22  
% 6.25/1.22  % (18220)Memory used [KB]: 14456
% 6.25/1.22  % (18220)Time elapsed: 0.782 s
% 6.25/1.22  % (18220)------------------------------
% 6.25/1.22  % (18220)------------------------------
% 6.25/1.23  % (18195)Success in time 0.861 s
%------------------------------------------------------------------------------
