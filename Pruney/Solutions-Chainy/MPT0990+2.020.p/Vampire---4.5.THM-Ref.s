%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:31 EST 2020

% Result     : Theorem 11.53s
% Output     : Refutation 11.53s
% Verified   : 
% Statistics : Number of formulae       :  489 (1639 expanded)
%              Number of leaves         :   93 ( 702 expanded)
%              Depth                    :   18
%              Number of atoms          : 2495 (6617 expanded)
%              Number of equality atoms :  443 (1270 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f107,f111,f133,f137,f141,f145,f149,f156,f160,f164,f171,f175,f212,f269,f273,f277,f281,f310,f334,f342,f374,f382,f390,f410,f424,f432,f505,f559,f602,f625,f713,f737,f770,f809,f813,f899,f1135,f1430,f1448,f1537,f1640,f1784,f2109,f2110,f2111,f2152,f2262,f7368,f7961,f8316,f8320,f8356,f8362,f8413,f8546,f8547,f8563,f8634,f8638,f8684,f8689,f9316,f9354,f9358,f9359,f9360,f9361,f9377,f9379])).

fof(f9379,plain,
    ( sK0 != k1_relat_1(sK2)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3)
    | sK2 != k2_funct_1(sK3)
    | sK2 != k2_funct_1(k2_funct_1(sK2))
    | sK3 != k2_funct_1(k2_funct_1(sK3))
    | r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))
    | ~ r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9377,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_52
    | ~ spl4_53
    | spl4_560
    | ~ spl4_570
    | ~ spl4_599 ),
    inference(avatar_contradiction_clause,[],[f9376])).

fof(f9376,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_39
    | ~ spl4_52
    | ~ spl4_53
    | spl4_560
    | ~ spl4_570
    | ~ spl4_599 ),
    inference(subsumption_resolution,[],[f9375,f431])).

fof(f431,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl4_39
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f9375,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52
    | ~ spl4_53
    | spl4_560
    | ~ spl4_570
    | ~ spl4_599 ),
    inference(forward_demodulation,[],[f7364,f9372])).

fof(f9372,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_570
    | ~ spl4_599 ),
    inference(subsumption_resolution,[],[f8348,f9367])).

fof(f9367,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_599 ),
    inference(avatar_component_clause,[],[f8678])).

fof(f8678,plain,
    ( spl4_599
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_599])])).

fof(f8348,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_570 ),
    inference(trivial_inequality_removal,[],[f8347])).

fof(f8347,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_570 ),
    inference(forward_demodulation,[],[f8346,f1538])).

fof(f1538,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_53 ),
    inference(avatar_component_clause,[],[f608])).

fof(f608,plain,
    ( spl4_53
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f8346,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3))
    | sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52
    | ~ spl4_570 ),
    inference(forward_demodulation,[],[f8345,f7960])).

fof(f7960,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_570 ),
    inference(avatar_component_clause,[],[f7959])).

fof(f7959,plain,
    ( spl4_570
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_570])])).

fof(f8345,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8344,f211])).

fof(f211,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f8344,plain,
    ( ~ v1_relat_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8329,f102])).

fof(f102,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_1
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f8329,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_52 ),
    inference(resolution,[],[f8315,f267])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) != sK1
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k2_funct_1(X0) = sK2 )
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f266,f252])).

fof(f252,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f222,f163])).

fof(f163,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl4_12
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f222,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f266,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k2_funct_1(X0) = sK2 )
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f129,f223])).

fof(f223,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f129,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK2)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
        | k2_funct_1(X0) = sK2 )
    | ~ spl4_3 ),
    inference(resolution,[],[f110,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f110,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl4_3
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f8315,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl4_52
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f7364,plain,
    ( k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | spl4_560 ),
    inference(avatar_component_clause,[],[f7363])).

fof(f7363,plain,
    ( spl4_560
  <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_560])])).

fof(f9361,plain,
    ( k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) != k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | sK1 = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9360,plain,
    ( k1_relat_1(sK3) != k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9359,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3))
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(sK1)
    | r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1))
    | ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f9358,plain,
    ( spl4_618
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_570 ),
    inference(avatar_split_clause,[],[f8278,f7959,f2260,f1638,f1540,f1428,f173,f162,f158,f147,f139,f131,f109,f101,f9356])).

fof(f9356,plain,
    ( spl4_618
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_618])])).

fof(f131,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f139,plain,
    ( spl4_6
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f147,plain,
    ( spl4_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f158,plain,
    ( spl4_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f1428,plain,
    ( spl4_113
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).

fof(f1540,plain,
    ( spl4_119
  <=> sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).

fof(f1638,plain,
    ( spl4_131
  <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).

fof(f2260,plain,
    ( spl4_164
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).

fof(f8278,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_570 ),
    inference(subsumption_resolution,[],[f8246,f8273])).

fof(f8273,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(subsumption_resolution,[],[f8272,f94])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f8272,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(forward_demodulation,[],[f1525,f7960])).

fof(f1525,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1524,f132])).

fof(f132,plain,
    ( k1_xboole_0 != sK0
    | spl4_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1524,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1523,f163])).

fof(f1523,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1522,f110])).

fof(f1522,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1521,f159])).

fof(f159,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f158])).

fof(f1521,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1520,f140])).

fof(f140,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f1520,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1519,f102])).

fof(f1519,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1518,f174])).

fof(f1518,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_8
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1516,f148])).

fof(f148,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1516,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3)
    | ~ spl4_113 ),
    inference(superposition,[],[f77,f1429])).

fof(f1429,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl4_113 ),
    inference(avatar_component_clause,[],[f1428])).

fof(f77,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X3)
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f8246,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | spl4_4
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164 ),
    inference(forward_demodulation,[],[f8245,f85])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f8245,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_1
    | spl4_4
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f8244,f132])).

fof(f8244,plain,
    ( ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f8243,f1541])).

fof(f1541,plain,
    ( sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ spl4_119 ),
    inference(avatar_component_clause,[],[f1540])).

fof(f8243,plain,
    ( sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_131
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f8242,f102])).

fof(f8242,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_131
    | ~ spl4_164 ),
    inference(subsumption_resolution,[],[f2411,f1639])).

fof(f1639,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ spl4_131 ),
    inference(avatar_component_clause,[],[f1638])).

fof(f2411,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ v1_funct_1(sK3)
    | sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | ~ spl4_164 ),
    inference(resolution,[],[f2261,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f2261,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl4_164 ),
    inference(avatar_component_clause,[],[f2260])).

fof(f9354,plain,
    ( spl4_617
    | ~ spl4_601 ),
    inference(avatar_split_clause,[],[f8718,f8687,f9352])).

fof(f9352,plain,
    ( spl4_617
  <=> r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_617])])).

fof(f8687,plain,
    ( spl4_601
  <=> m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_601])])).

fof(f8718,plain,
    ( r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3)))
    | ~ spl4_601 ),
    inference(resolution,[],[f8688,f98])).

fof(f98,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r2_relset_1(X0,X1,X3,X3) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 != X3
      | r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f8688,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_601 ),
    inference(avatar_component_clause,[],[f8687])).

fof(f9316,plain,
    ( ~ spl4_611
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_582
    | ~ spl4_590
    | spl4_597 ),
    inference(avatar_split_clause,[],[f8676,f8668,f8632,f8561,f8354,f594,f275,f158,f139,f101,f9314])).

fof(f9314,plain,
    ( spl4_611
  <=> r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_611])])).

fof(f275,plain,
    ( spl4_17
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f594,plain,
    ( spl4_50
  <=> v1_funct_2(k2_funct_1(sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f8354,plain,
    ( spl4_575
  <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_575])])).

fof(f8561,plain,
    ( spl4_582
  <=> k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_582])])).

fof(f8632,plain,
    ( spl4_590
  <=> k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_590])])).

fof(f8668,plain,
    ( spl4_597
  <=> sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_597])])).

fof(f8676,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_582
    | ~ spl4_590
    | spl4_597 ),
    inference(subsumption_resolution,[],[f8659,f8675])).

fof(f8675,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ spl4_582
    | spl4_597 ),
    inference(superposition,[],[f8669,f8562])).

fof(f8562,plain,
    ( k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_582 ),
    inference(avatar_component_clause,[],[f8561])).

fof(f8669,plain,
    ( sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | spl4_597 ),
    inference(avatar_component_clause,[],[f8668])).

fof(f8659,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_582
    | ~ spl4_590 ),
    inference(forward_demodulation,[],[f8658,f8562])).

fof(f8658,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(forward_demodulation,[],[f8657,f85])).

fof(f8657,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8656,f276])).

fof(f276,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f275])).

fof(f8656,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8655,f159])).

fof(f8655,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8654,f140])).

fof(f8654,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8653,f102])).

fof(f8653,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_50
    | ~ spl4_575
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8652,f8355])).

fof(f8355,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_575 ),
    inference(avatar_component_clause,[],[f8354])).

fof(f8652,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_50
    | ~ spl4_590 ),
    inference(subsumption_resolution,[],[f8651,f595])).

fof(f595,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK0,sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f594])).

fof(f8651,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1))
    | ~ v1_funct_2(k2_funct_1(sK3),sK0,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_590 ),
    inference(superposition,[],[f84,f8633])).

fof(f8633,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3))
    | ~ spl4_590 ),
    inference(avatar_component_clause,[],[f8632])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f8689,plain,
    ( spl4_601
    | ~ spl4_590
    | ~ spl4_600 ),
    inference(avatar_split_clause,[],[f8685,f8682,f8632,f8687])).

fof(f8682,plain,
    ( spl4_600
  <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_600])])).

fof(f8685,plain,
    ( m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_590
    | ~ spl4_600 ),
    inference(forward_demodulation,[],[f8683,f8633])).

fof(f8683,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_600 ),
    inference(avatar_component_clause,[],[f8682])).

fof(f8684,plain,
    ( spl4_600
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_575 ),
    inference(avatar_split_clause,[],[f8468,f8354,f275,f158,f101,f8682])).

fof(f8468,plain,
    ( m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_575 ),
    inference(subsumption_resolution,[],[f8428,f276])).

fof(f8428,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_575 ),
    inference(resolution,[],[f8355,f203])).

fof(f203,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | m1_subset_1(k1_partfun1(sK1,sK0,X5,X6,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f183,f102])).

fof(f183,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | m1_subset_1(k1_partfun1(sK1,sK0,X5,X6,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X6))) )
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f87])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f8638,plain,
    ( spl4_591
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f8339,f600,f154,f101,f8636])).

fof(f8636,plain,
    ( spl4_591
  <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_591])])).

fof(f8339,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8338,f211])).

fof(f8338,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8327,f102])).

fof(f8327,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_52 ),
    inference(resolution,[],[f8315,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f8634,plain,
    ( spl4_590
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_570
    | ~ spl4_575 ),
    inference(avatar_split_clause,[],[f8470,f8354,f7959,f2260,f1638,f1540,f1428,f275,f173,f162,f158,f147,f139,f131,f109,f101,f8632])).

fof(f8470,plain,
    ( k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_570
    | ~ spl4_575 ),
    inference(forward_demodulation,[],[f8469,f8278])).

fof(f8469,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_575 ),
    inference(subsumption_resolution,[],[f8429,f276])).

fof(f8429,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_575 ),
    inference(resolution,[],[f8355,f204])).

fof(f204,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X7)
        | k1_partfun1(sK1,sK0,X8,X9,sK3,X7) = k5_relat_1(sK3,X7) )
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f184,f102])).

fof(f184,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k1_partfun1(sK1,sK0,X8,X9,sK3,X7) = k5_relat_1(sK3,X7) )
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f8563,plain,
    ( spl4_582
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52
    | ~ spl4_575 ),
    inference(avatar_split_clause,[],[f8466,f8354,f600,f154,f101,f8561])).

fof(f8466,plain,
    ( k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52
    | ~ spl4_575 ),
    inference(forward_demodulation,[],[f8424,f8339])).

fof(f8424,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k2_relset_1(sK0,sK1,k2_funct_1(sK3))
    | ~ spl4_575 ),
    inference(resolution,[],[f8355,f89])).

fof(f8547,plain,
    ( k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f8546,plain,
    ( spl4_581
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_384
    | ~ spl4_570
    | ~ spl4_576 ),
    inference(avatar_split_clause,[],[f8521,f8360,f7959,f4788,f2260,f1638,f1540,f1428,f608,f600,f275,f173,f162,f158,f154,f151,f147,f139,f131,f109,f101,f8544])).

fof(f8544,plain,
    ( spl4_581
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_581])])).

fof(f151,plain,
    ( spl4_9
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f4788,plain,
    ( spl4_384
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_384])])).

fof(f8360,plain,
    ( spl4_576
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_576])])).

fof(f8521,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_17
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_113
    | ~ spl4_119
    | ~ spl4_131
    | ~ spl4_164
    | ~ spl4_384
    | ~ spl4_570
    | ~ spl4_576 ),
    inference(subsumption_resolution,[],[f8520,f8278])).

fof(f8520,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_384
    | ~ spl4_576 ),
    inference(forward_demodulation,[],[f8519,f8339])).

fof(f8519,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_53
    | ~ spl4_384
    | ~ spl4_576 ),
    inference(subsumption_resolution,[],[f8518,f1538])).

fof(f8518,plain,
    ( sK0 != k2_relat_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_384
    | ~ spl4_576 ),
    inference(forward_demodulation,[],[f8517,f8361])).

fof(f8361,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_576 ),
    inference(avatar_component_clause,[],[f8360])).

fof(f8517,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_17
    | ~ spl4_384 ),
    inference(subsumption_resolution,[],[f8516,f276])).

fof(f8516,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_11
    | ~ spl4_384 ),
    inference(subsumption_resolution,[],[f8500,f152])).

fof(f152,plain,
    ( v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f151])).

fof(f8500,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3)))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_11
    | ~ spl4_384 ),
    inference(resolution,[],[f8412,f207])).

fof(f207,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK3)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK3,X0)
        | k2_funct_1(X0) = sK3 )
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f116,f186])).

fof(f186,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f90])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(sK3)
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK3,X0)
        | k2_funct_1(X0) = sK3 )
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f67])).

fof(f8412,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_384 ),
    inference(avatar_component_clause,[],[f4788])).

fof(f8413,plain,
    ( spl4_384
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_53
    | ~ spl4_573
    | ~ spl4_576 ),
    inference(avatar_split_clause,[],[f8397,f8360,f8318,f608,f275,f154,f151,f101,f4788])).

fof(f8318,plain,
    ( spl4_573
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_573])])).

fof(f8397,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_53
    | ~ spl4_573
    | ~ spl4_576 ),
    inference(subsumption_resolution,[],[f8396,f1538])).

fof(f8396,plain,
    ( sK0 != k2_relat_1(sK3)
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_573
    | ~ spl4_576 ),
    inference(forward_demodulation,[],[f8391,f8361])).

fof(f8391,plain,
    ( k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_573 ),
    inference(subsumption_resolution,[],[f8390,f152])).

fof(f8390,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_573 ),
    inference(subsumption_resolution,[],[f8389,f102])).

fof(f8389,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_10
    | ~ spl4_17
    | ~ spl4_573 ),
    inference(subsumption_resolution,[],[f8388,f211])).

fof(f8388,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_17
    | ~ spl4_573 ),
    inference(subsumption_resolution,[],[f8387,f276])).

fof(f8387,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_573 ),
    inference(subsumption_resolution,[],[f8385,f94])).

fof(f8385,plain,
    ( ~ v2_funct_1(k6_relat_1(sK1))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | v2_funct_1(k2_funct_1(sK3))
    | ~ spl4_573 ),
    inference(superposition,[],[f81,f8319])).

fof(f8319,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)
    | ~ spl4_573 ),
    inference(avatar_component_clause,[],[f8318])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).

fof(f8362,plain,
    ( spl4_576
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f8337,f608,f600,f154,f101,f8360])).

fof(f8337,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52
    | ~ spl4_53 ),
    inference(forward_demodulation,[],[f8336,f1538])).

fof(f8336,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_10
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8335,f211])).

fof(f8335,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_52 ),
    inference(subsumption_resolution,[],[f8326,f102])).

fof(f8326,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_52 ),
    inference(resolution,[],[f8315,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8356,plain,
    ( spl4_575
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(avatar_split_clause,[],[f8275,f7959,f1428,f597,f173,f162,f158,f147,f139,f131,f109,f101,f8354])).

fof(f597,plain,
    ( spl4_51
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f8275,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(subsumption_resolution,[],[f8253,f8273])).

fof(f8253,plain,
    ( ~ v2_funct_1(sK3)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f193,f1542])).

fof(f1542,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_51 ),
    inference(avatar_component_clause,[],[f597])).

fof(f193,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f192,f102])).

fof(f192,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f178,f140])).

fof(f178,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f8320,plain,
    ( spl4_573
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(avatar_split_clause,[],[f8274,f7959,f1428,f597,f173,f162,f158,f147,f139,f131,f109,f101,f8318])).

fof(f8274,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_51
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(subsumption_resolution,[],[f8254,f8273])).

fof(f8254,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_51 ),
    inference(subsumption_resolution,[],[f197,f1542])).

fof(f197,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | ~ spl4_1
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f196,f85])).

fof(f196,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_1
    | spl4_4
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f195,f132])).

fof(f195,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f194,f102])).

fof(f194,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f179,f140])).

fof(f179,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f78])).

fof(f8316,plain,
    ( spl4_52
    | ~ spl4_1
    | ~ spl4_3
    | spl4_4
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_113
    | ~ spl4_570 ),
    inference(avatar_split_clause,[],[f8273,f7959,f1428,f173,f162,f158,f147,f139,f131,f109,f101,f600])).

fof(f7961,plain,
    ( spl4_570
    | ~ spl4_59
    | ~ spl4_76
    | ~ spl4_150 ),
    inference(avatar_split_clause,[],[f7957,f2150,f897,f768,f7959])).

fof(f768,plain,
    ( spl4_59
  <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f897,plain,
    ( spl4_76
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f2150,plain,
    ( spl4_150
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).

fof(f7957,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_59
    | ~ spl4_76
    | ~ spl4_150 ),
    inference(subsumption_resolution,[],[f7955,f769])).

fof(f769,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f768])).

fof(f7955,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_76
    | ~ spl4_150 ),
    inference(resolution,[],[f1042,f2151])).

fof(f2151,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_150 ),
    inference(avatar_component_clause,[],[f2150])).

fof(f1042,plain,
    ( ! [X0] :
        ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0)
        | k5_relat_1(sK2,sK3) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
    | ~ spl4_76 ),
    inference(resolution,[],[f898,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f898,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_76 ),
    inference(avatar_component_clause,[],[f897])).

fof(f7368,plain,
    ( ~ spl4_559
    | ~ spl4_560
    | spl4_561
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_46
    | ~ spl4_55 ),
    inference(avatar_split_clause,[],[f2101,f711,f503,f388,f380,f340,f279,f275,f166,f151,f7366,f7363,f7360])).

fof(f7360,plain,
    ( spl4_559
  <=> sK1 = k2_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_559])])).

fof(f7366,plain,
    ( spl4_561
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_561])])).

fof(f166,plain,
    ( spl4_13
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f279,plain,
    ( spl4_18
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f340,plain,
    ( spl4_27
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f380,plain,
    ( spl4_32
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f388,plain,
    ( spl4_34
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f503,plain,
    ( spl4_46
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f711,plain,
    ( spl4_55
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f2101,plain,
    ( sK2 = k2_funct_1(sK3)
    | k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | sK1 != k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_46
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f2100,f712])).

fof(f712,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f711])).

fof(f2100,plain,
    ( k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | sK1 != k2_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f2099,f389])).

fof(f389,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_34 ),
    inference(avatar_component_clause,[],[f388])).

fof(f2099,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | sK1 != k2_relat_1(k2_funct_1(sK3))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f2098,f381])).

fof(f381,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f380])).

fof(f2098,plain,
    ( sK1 != k2_relat_1(k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f2097,f341])).

fof(f341,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f340])).

fof(f2097,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_18
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f2096,f280])).

fof(f280,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f279])).

fof(f2096,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_13
    | ~ spl4_17
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f2091,f167])).

fof(f167,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f166])).

fof(f2091,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3))
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))
    | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_9
    | ~ spl4_17
    | ~ spl4_46 ),
    inference(resolution,[],[f291,f504])).

fof(f504,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f503])).

fof(f291,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK3))
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(k2_funct_1(sK3),X0)
        | k2_funct_1(X0) = k2_funct_1(sK3) )
    | ~ spl4_9
    | ~ spl4_17 ),
    inference(subsumption_resolution,[],[f286,f152])).

fof(f286,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_relat_1(k2_funct_1(sK3))
        | ~ v1_relat_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK3))
        | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(k2_funct_1(sK3),X0)
        | k2_funct_1(X0) = k2_funct_1(sK3) )
    | ~ spl4_17 ),
    inference(resolution,[],[f276,f67])).

fof(f2262,plain,
    ( spl4_164
    | ~ spl4_48
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f1559,f608,f557,f2260])).

fof(f557,plain,
    ( spl4_48
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f1559,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))
    | ~ spl4_48
    | ~ spl4_53 ),
    inference(superposition,[],[f558,f1538])).

fof(f558,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f557])).

fof(f2152,plain,
    ( spl4_150
    | ~ spl4_16
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f1514,f1428,f271,f2150])).

fof(f271,plain,
    ( spl4_16
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f1514,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_16
    | ~ spl4_113 ),
    inference(superposition,[],[f272,f1429])).

fof(f272,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f271])).

fof(f2111,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2110,plain,
    ( k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | sK0 != k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | k2_relat_1(sK3) = k1_relat_1(sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2109,plain,
    ( spl4_144
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_62
    | ~ spl4_115 ),
    inference(avatar_split_clause,[],[f1574,f1446,f807,f422,f332,f279,f173,f147,f109,f2107])).

fof(f2107,plain,
    ( spl4_144
  <=> sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).

fof(f332,plain,
    ( spl4_25
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f422,plain,
    ( spl4_37
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f807,plain,
    ( spl4_62
  <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).

fof(f1446,plain,
    ( spl4_115
  <=> k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).

fof(f1574,plain,
    ( sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_62
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1573,f808])).

fof(f808,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl4_62 ),
    inference(avatar_component_clause,[],[f807])).

fof(f1573,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(forward_demodulation,[],[f1572,f85])).

fof(f1572,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1571,f280])).

fof(f1571,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1570,f174])).

fof(f1570,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1569,f148])).

fof(f1569,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1568,f110])).

fof(f1568,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_25
    | ~ spl4_37
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1567,f423])).

fof(f423,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f422])).

fof(f1567,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_25
    | ~ spl4_115 ),
    inference(subsumption_resolution,[],[f1566,f333])).

fof(f333,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f332])).

fof(f1566,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_115 ),
    inference(superposition,[],[f84,f1447])).

fof(f1447,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_115 ),
    inference(avatar_component_clause,[],[f1446])).

fof(f1784,plain,
    ( spl4_51
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_113 ),
    inference(avatar_split_clause,[],[f1544,f1428,f271,f173,f158,f147,f139,f109,f101,f597])).

fof(f1544,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1543,f1514])).

fof(f1543,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(forward_demodulation,[],[f1532,f85])).

fof(f1532,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1531,f102])).

fof(f1531,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_15
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1530,f174])).

fof(f1530,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_11
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1529,f148])).

fof(f1529,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1528,f110])).

fof(f1528,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_6
    | ~ spl4_11
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1527,f159])).

fof(f1527,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_6
    | ~ spl4_113 ),
    inference(subsumption_resolution,[],[f1517,f140])).

fof(f1517,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_113 ),
    inference(superposition,[],[f84,f1429])).

fof(f1640,plain,
    ( spl4_131
    | ~ spl4_30
    | ~ spl4_53 ),
    inference(avatar_split_clause,[],[f1558,f608,f372,f1638])).

fof(f372,plain,
    ( spl4_30
  <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f1558,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0)
    | ~ spl4_30
    | ~ spl4_53 ),
    inference(superposition,[],[f373,f1538])).

fof(f373,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f372])).

fof(f1537,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3)
    | sK0 = k2_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1448,plain,
    ( spl4_115
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f656,f430,f422,f279,f173,f109,f1446])).

fof(f656,plain,
    ( k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f655,f431])).

fof(f655,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f650,f280])).

fof(f650,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(resolution,[],[f251,f423])).

fof(f251,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_1(X7)
        | k1_partfun1(sK0,sK1,X8,X9,sK2,X7) = k5_relat_1(sK2,X7) )
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f221,f110])).

fof(f221,plain,
    ( ! [X8,X7,X9] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k1_partfun1(sK0,sK1,X8,X9,sK2,X7) = k5_relat_1(sK2,X7) )
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f88])).

fof(f1430,plain,
    ( spl4_113
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f651,f173,f158,f109,f101,f1428])).

fof(f651,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f646,f102])).

fof(f646,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(resolution,[],[f251,f159])).

fof(f1135,plain,
    ( spl4_82
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f569,f557,f1133])).

fof(f1133,plain,
    ( spl4_82
  <=> k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).

fof(f569,plain,
    ( k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)
    | ~ spl4_48 ),
    inference(resolution,[],[f558,f89])).

fof(f899,plain,
    ( spl4_76
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f688,f173,f158,f109,f101,f897])).

fof(f688,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f687,f651])).

fof(f687,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f682,f102])).

fof(f682,plain,
    ( ~ v1_funct_1(sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_15 ),
    inference(resolution,[],[f250,f159])).

fof(f250,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | ~ v1_funct_1(X4)
        | m1_subset_1(k1_partfun1(sK0,sK1,X5,X6,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) )
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f220,f110])).

fof(f220,plain,
    ( ! [X6,X4,X5] :
        ( ~ v1_funct_1(sK2)
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X5,X6,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(sK0,X6))) )
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f87])).

fof(f813,plain,
    ( spl4_63
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f480,f422,f380,f811])).

fof(f811,plain,
    ( spl4_63
  <=> k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f480,plain,
    ( k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_32
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f462,f381])).

fof(f462,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ spl4_37 ),
    inference(resolution,[],[f423,f89])).

fof(f809,plain,
    ( spl4_62
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f782,f768,f807])).

fof(f782,plain,
    ( r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | ~ spl4_59 ),
    inference(resolution,[],[f769,f98])).

fof(f770,plain,
    ( spl4_59
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f696,f430,f422,f279,f173,f109,f768])).

fof(f696,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f695,f656])).

fof(f695,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f686,f280])).

fof(f686,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_3
    | ~ spl4_15
    | ~ spl4_37 ),
    inference(resolution,[],[f250,f423])).

fof(f737,plain,
    ( spl4_56
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f464,f422,f735])).

fof(f735,plain,
    ( spl4_56
  <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f464,plain,
    ( r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2))
    | ~ spl4_37 ),
    inference(resolution,[],[f423,f98])).

fof(f713,plain,
    ( spl4_55
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f709,f503,f430,f388,f380,f340,f279,f173,f166,f162,f109,f711])).

fof(f709,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_39
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f708,f431])).

fof(f708,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_34
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f707,f389])).

fof(f707,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_32
    | ~ spl4_46 ),
    inference(forward_demodulation,[],[f706,f381])).

fof(f706,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f705,f341])).

fof(f705,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f704,f167])).

fof(f704,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_18
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f699,f280])).

fof(f699,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | sK1 != k1_relat_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_46 ),
    inference(resolution,[],[f267,f504])).

fof(f625,plain,
    ( ~ spl4_54
    | spl4_7
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f606,f422,f158,f143,f623])).

fof(f623,plain,
    ( spl4_54
  <=> r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f143,plain,
    ( spl4_7
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f606,plain,
    ( ~ r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))
    | spl4_7
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f605,f144])).

fof(f144,plain,
    ( sK3 != k2_funct_1(sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f143])).

fof(f605,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))
    | ~ spl4_11
    | ~ spl4_37 ),
    inference(resolution,[],[f181,f423])).

fof(f181,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | sK3 = X0
        | ~ r2_relset_1(sK1,sK0,sK3,X0) )
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f83])).

fof(f602,plain,
    ( spl4_50
    | ~ spl4_51
    | ~ spl4_52
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f191,f158,f139,f101,f600,f597,f594])).

fof(f191,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | v1_funct_2(k2_funct_1(sK3),sK0,sK1)
    | ~ spl4_1
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f190,f102])).

fof(f190,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | v1_funct_2(k2_funct_1(sK3),sK0,sK1)
    | ~ spl4_6
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f177,f140])).

fof(f177,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | v1_funct_2(k2_funct_1(sK3),sK0,sK1)
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f559,plain,
    ( spl4_48
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f209,f158,f101,f557])).

fof(f209,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f113,f186])).

fof(f113,plain,
    ( ~ v1_relat_1(sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f505,plain,
    ( spl4_46
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_27
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f493,f430,f340,f308,f279,f169,f166,f109,f503])).

fof(f169,plain,
    ( spl4_14
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f308,plain,
    ( spl4_19
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f493,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_27
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f492,f309])).

fof(f309,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f308])).

fof(f492,plain,
    ( sK1 != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_27
    | ~ spl4_39 ),
    inference(forward_demodulation,[],[f491,f341])).

fof(f491,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_13
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f490,f167])).

fof(f490,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f489,f110])).

fof(f489,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_14
    | ~ spl4_18
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f488,f268])).

fof(f268,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f169])).

fof(f488,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_18
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f487,f280])).

fof(f487,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_39 ),
    inference(subsumption_resolution,[],[f486,f94])).

fof(f486,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ spl4_39 ),
    inference(superposition,[],[f81,f431])).

fof(f432,plain,
    ( spl4_39
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f242,f173,f162,f147,f135,f109,f105,f430])).

fof(f105,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f135,plain,
    ( spl4_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f242,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f241,f85])).

fof(f241,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f240,f136])).

fof(f136,plain,
    ( k1_xboole_0 != sK1
    | spl4_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f240,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f239,f106])).

fof(f106,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f239,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f238,f163])).

fof(f238,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f237,f110])).

fof(f237,plain,
    ( ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f216,f148])).

fof(f216,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f78])).

fof(f424,plain,
    ( spl4_37
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f236,f173,f162,f147,f109,f105,f422])).

fof(f236,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f235,f163])).

fof(f235,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f234,f106])).

fof(f234,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f233,f110])).

fof(f233,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f215,f148])).

fof(f215,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f66])).

fof(f410,plain,
    ( spl4_36
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f185,f158,f408])).

fof(f408,plain,
    ( spl4_36
  <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f185,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_11 ),
    inference(resolution,[],[f159,f89])).

fof(f390,plain,
    ( spl4_34
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f259,f173,f162,f147,f135,f109,f105,f388])).

fof(f259,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_5
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f258,f242])).

fof(f258,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f123,f223])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f119,f110])).

fof(f119,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f382,plain,
    ( spl4_32
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f257,f173,f109,f105,f380])).

fof(f257,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f122,f223])).

fof(f122,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f118,f110])).

fof(f118,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f71])).

fof(f374,plain,
    ( spl4_30
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f210,f158,f101,f372])).

fof(f210,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f112,f186])).

fof(f112,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f342,plain,
    ( spl4_27
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f256,f173,f162,f109,f105,f340])).

fof(f256,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f255,f252])).

fof(f255,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f121,f223])).

fof(f121,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f117,f110])).

fof(f117,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f70])).

fof(f334,plain,
    ( spl4_25
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f232,f173,f162,f147,f109,f105,f332])).

fof(f232,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f231,f163])).

fof(f231,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f230,f106])).

fof(f230,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f229,f110])).

fof(f229,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f214,f148])).

fof(f214,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f65])).

fof(f310,plain,
    ( spl4_19
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f252,f173,f162,f308])).

fof(f281,plain,
    ( spl4_18
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f228,f173,f162,f147,f109,f105,f279])).

fof(f228,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f227,f163])).

fof(f227,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f226,f106])).

fof(f226,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_3
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f225,f110])).

fof(f225,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_8
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f213,f148])).

fof(f213,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f174,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f277,plain,
    ( spl4_17
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f208,f158,f101,f275])).

fof(f208,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_1
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f115,f186])).

fof(f115,plain,
    ( ~ v1_relat_1(sK3)
    | v1_funct_1(k2_funct_1(sK3))
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f273,plain,(
    spl4_16 ),
    inference(avatar_split_clause,[],[f99,f271])).

fof(f99,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f85])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f269,plain,
    ( spl4_14
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f223,f173,f169])).

fof(f212,plain,
    ( spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f186,f158,f154])).

fof(f175,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f63,f173])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f171,plain,
    ( spl4_13
    | ~ spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f127,f109,f169,f166])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f110,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f164,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f55,f162])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f160,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f54,f158])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f156,plain,
    ( spl4_9
    | ~ spl4_10
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f114,f101,f154,f151])).

fof(f114,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_1 ),
    inference(resolution,[],[f102,f72])).

fof(f149,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f62,f147])).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f145,plain,(
    ~ spl4_7 ),
    inference(avatar_split_clause,[],[f60,f143])).

fof(f60,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f141,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f53,f139])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f137,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f59,f135])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f133,plain,(
    ~ spl4_4 ),
    inference(avatar_split_clause,[],[f58,f131])).

fof(f58,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f111,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f61,f109])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f103,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f52,f101])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:20:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (15191)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.48  % (15207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (15179)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (15180)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.44/0.54  % (15189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.44/0.55  % (15194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.55  % (15194)Refutation not found, incomplete strategy% (15194)------------------------------
% 1.44/0.55  % (15194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (15194)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (15194)Memory used [KB]: 10746
% 1.44/0.55  % (15194)Time elapsed: 0.149 s
% 1.44/0.55  % (15194)------------------------------
% 1.44/0.55  % (15194)------------------------------
% 1.44/0.55  % (15205)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.56  % (15202)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.44/0.57  % (15181)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.44/0.57  % (15200)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.44/0.57  % (15192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.44/0.57  % (15186)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.44/0.57  % (15190)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.57  % (15188)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.58  % (15184)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.59  % (15203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.44/0.59  % (15183)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.44/0.59  % (15182)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.44/0.60  % (15195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.44/0.60  % (15204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.44/0.61  % (15178)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.44/0.61  % (15187)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.61  % (15199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.62  % (15185)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.44/0.62  % (15197)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.63  % (15201)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.63  % (15206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.10/0.64  % (15193)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 2.10/0.64  % (15198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 2.10/0.64  % (15196)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 2.10/0.67  % (15232)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.67/0.85  % (15180)Time limit reached!
% 3.67/0.85  % (15180)------------------------------
% 3.67/0.85  % (15180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.85  % (15202)Time limit reached!
% 3.67/0.85  % (15202)------------------------------
% 3.67/0.85  % (15202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.67/0.85  % (15202)Termination reason: Time limit
% 3.67/0.85  % (15202)Termination phase: Saturation
% 3.67/0.85  
% 3.67/0.85  % (15202)Memory used [KB]: 12409
% 3.67/0.85  % (15202)Time elapsed: 0.400 s
% 3.67/0.85  % (15202)------------------------------
% 3.67/0.85  % (15202)------------------------------
% 3.67/0.85  % (15180)Termination reason: Time limit
% 3.67/0.85  % (15180)Termination phase: Saturation
% 3.67/0.85  
% 3.67/0.85  % (15180)Memory used [KB]: 6908
% 3.67/0.85  % (15180)Time elapsed: 0.400 s
% 3.67/0.85  % (15180)------------------------------
% 3.67/0.85  % (15180)------------------------------
% 4.36/0.94  % (15207)Time limit reached!
% 4.36/0.94  % (15207)------------------------------
% 4.36/0.94  % (15207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.94  % (15207)Termination reason: Time limit
% 4.36/0.94  
% 4.36/0.94  % (15207)Memory used [KB]: 7803
% 4.36/0.94  % (15207)Time elapsed: 0.520 s
% 4.36/0.94  % (15207)------------------------------
% 4.36/0.94  % (15207)------------------------------
% 4.36/0.96  % (15235)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 4.36/0.99  % (15234)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 4.36/0.99  % (15184)Time limit reached!
% 4.36/0.99  % (15184)------------------------------
% 4.36/0.99  % (15184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.00  % (15192)Time limit reached!
% 4.79/1.00  % (15192)------------------------------
% 4.79/1.00  % (15192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.01  % (15184)Termination reason: Time limit
% 4.79/1.01  % (15184)Termination phase: Saturation
% 4.79/1.01  
% 4.79/1.01  % (15184)Memory used [KB]: 13944
% 4.79/1.01  % (15184)Time elapsed: 0.500 s
% 4.79/1.01  % (15184)------------------------------
% 4.79/1.01  % (15184)------------------------------
% 4.79/1.01  % (15192)Termination reason: Time limit
% 4.79/1.01  % (15192)Termination phase: Saturation
% 4.79/1.01  
% 4.79/1.01  % (15192)Memory used [KB]: 5245
% 4.79/1.01  % (15192)Time elapsed: 0.500 s
% 4.79/1.01  % (15192)------------------------------
% 4.79/1.01  % (15192)------------------------------
% 4.79/1.01  % (15185)Time limit reached!
% 4.79/1.01  % (15185)------------------------------
% 4.79/1.01  % (15185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.79/1.01  % (15185)Termination reason: Time limit
% 4.79/1.01  
% 4.79/1.01  % (15185)Memory used [KB]: 4861
% 4.79/1.01  % (15185)Time elapsed: 0.608 s
% 4.79/1.01  % (15185)------------------------------
% 4.79/1.01  % (15185)------------------------------
% 5.62/1.07  % (15237)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 5.92/1.12  % (15265)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.92/1.13  % (15266)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 6.20/1.15  % (15268)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 6.20/1.20  % (15179)Time limit reached!
% 6.20/1.20  % (15179)------------------------------
% 6.20/1.20  % (15179)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.20  % (15179)Termination reason: Time limit
% 6.20/1.20  % (15179)Termination phase: Saturation
% 6.20/1.20  
% 6.20/1.20  % (15179)Memory used [KB]: 6268
% 6.20/1.20  % (15179)Time elapsed: 0.800 s
% 6.20/1.20  % (15179)------------------------------
% 6.20/1.20  % (15179)------------------------------
% 7.22/1.31  % (15181)Time limit reached!
% 7.22/1.31  % (15181)------------------------------
% 7.22/1.31  % (15181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.22/1.32  % (15181)Termination reason: Time limit
% 7.22/1.32  % (15181)Termination phase: Saturation
% 7.22/1.32  
% 7.22/1.32  % (15181)Memory used [KB]: 7547
% 7.22/1.32  % (15181)Time elapsed: 0.900 s
% 7.22/1.32  % (15181)------------------------------
% 7.22/1.32  % (15181)------------------------------
% 7.22/1.32  % (15370)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 8.26/1.43  % (15190)Time limit reached!
% 8.26/1.43  % (15190)------------------------------
% 8.26/1.43  % (15190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.26/1.43  % (15190)Termination reason: Time limit
% 8.26/1.43  % (15190)Termination phase: Saturation
% 8.26/1.43  
% 8.26/1.43  % (15190)Memory used [KB]: 18293
% 8.26/1.43  % (15190)Time elapsed: 1.0000 s
% 8.26/1.43  % (15190)------------------------------
% 8.26/1.43  % (15190)------------------------------
% 8.51/1.45  % (15404)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 8.51/1.50  % (15433)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 8.51/1.52  % (15205)Time limit reached!
% 8.51/1.52  % (15205)------------------------------
% 8.51/1.52  % (15205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.51/1.52  % (15205)Termination reason: Time limit
% 8.51/1.52  
% 8.51/1.52  % (15205)Memory used [KB]: 14072
% 8.51/1.52  % (15205)Time elapsed: 1.092 s
% 8.51/1.52  % (15205)------------------------------
% 8.51/1.52  % (15205)------------------------------
% 9.42/1.61  % (15178)Time limit reached!
% 9.42/1.61  % (15178)------------------------------
% 9.42/1.61  % (15178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.42/1.61  % (15178)Termination reason: Time limit
% 9.42/1.61  
% 9.42/1.61  % (15178)Memory used [KB]: 3070
% 9.42/1.61  % (15178)Time elapsed: 1.209 s
% 9.42/1.61  % (15178)------------------------------
% 9.42/1.61  % (15178)------------------------------
% 9.42/1.64  % (15268)Time limit reached!
% 9.42/1.64  % (15268)------------------------------
% 9.42/1.64  % (15268)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.42/1.64  % (15268)Termination reason: Time limit
% 9.42/1.64  % (15268)Termination phase: Saturation
% 9.42/1.64  
% 9.42/1.64  % (15268)Memory used [KB]: 17654
% 9.42/1.64  % (15268)Time elapsed: 0.600 s
% 9.42/1.64  % (15268)------------------------------
% 9.42/1.64  % (15268)------------------------------
% 10.39/1.70  % (15471)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 10.39/1.70  % (15475)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 10.78/1.75  % (15476)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.94/1.75  % (15183)Time limit reached!
% 10.94/1.75  % (15183)------------------------------
% 10.94/1.75  % (15183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.94/1.75  % (15183)Termination reason: Time limit
% 10.94/1.75  
% 10.94/1.75  % (15183)Memory used [KB]: 11129
% 10.94/1.75  % (15183)Time elapsed: 1.325 s
% 10.94/1.75  % (15183)------------------------------
% 10.94/1.75  % (15183)------------------------------
% 10.94/1.78  % (15235)Time limit reached!
% 10.94/1.78  % (15235)------------------------------
% 10.94/1.78  % (15235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.94/1.78  % (15235)Termination reason: Time limit
% 10.94/1.78  
% 10.94/1.78  % (15235)Memory used [KB]: 14583
% 10.94/1.78  % (15235)Time elapsed: 0.828 s
% 10.94/1.78  % (15235)------------------------------
% 10.94/1.78  % (15235)------------------------------
% 11.53/1.84  % (15204)Refutation found. Thanks to Tanya!
% 11.53/1.84  % SZS status Theorem for theBenchmark
% 11.53/1.85  % SZS output start Proof for theBenchmark
% 11.53/1.85  fof(f9380,plain,(
% 11.53/1.85    $false),
% 11.53/1.85    inference(avatar_sat_refutation,[],[f103,f107,f111,f133,f137,f141,f145,f149,f156,f160,f164,f171,f175,f212,f269,f273,f277,f281,f310,f334,f342,f374,f382,f390,f410,f424,f432,f505,f559,f602,f625,f713,f737,f770,f809,f813,f899,f1135,f1430,f1448,f1537,f1640,f1784,f2109,f2110,f2111,f2152,f2262,f7368,f7961,f8316,f8320,f8356,f8362,f8413,f8546,f8547,f8563,f8634,f8638,f8684,f8689,f9316,f9354,f9358,f9359,f9360,f9361,f9377,f9379])).
% 11.53/1.85  fof(f9379,plain,(
% 11.53/1.85    sK0 != k1_relat_1(sK2) | sK0 != k2_relset_1(sK1,sK0,sK3) | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3) | sK2 != k2_funct_1(sK3) | sK2 != k2_funct_1(k2_funct_1(sK2)) | sK3 != k2_funct_1(k2_funct_1(sK3)) | r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) | ~r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2))),
% 11.53/1.85    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.85  fof(f9377,plain,(
% 11.53/1.85    ~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_39 | ~spl4_52 | ~spl4_53 | spl4_560 | ~spl4_570 | ~spl4_599),
% 11.53/1.85    inference(avatar_contradiction_clause,[],[f9376])).
% 11.53/1.85  fof(f9376,plain,(
% 11.53/1.85    $false | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_39 | ~spl4_52 | ~spl4_53 | spl4_560 | ~spl4_570 | ~spl4_599)),
% 11.53/1.85    inference(subsumption_resolution,[],[f9375,f431])).
% 11.53/1.85  fof(f431,plain,(
% 11.53/1.85    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_39),
% 11.53/1.85    inference(avatar_component_clause,[],[f430])).
% 11.53/1.85  fof(f430,plain,(
% 11.53/1.85    spl4_39 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 11.53/1.85  fof(f9375,plain,(
% 11.53/1.85    k6_relat_1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52 | ~spl4_53 | spl4_560 | ~spl4_570 | ~spl4_599)),
% 11.53/1.85    inference(forward_demodulation,[],[f7364,f9372])).
% 11.53/1.85  fof(f9372,plain,(
% 11.53/1.85    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52 | ~spl4_53 | ~spl4_570 | ~spl4_599)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8348,f9367])).
% 11.53/1.85  fof(f9367,plain,(
% 11.53/1.85    sK1 = k1_relat_1(sK3) | ~spl4_599),
% 11.53/1.85    inference(avatar_component_clause,[],[f8678])).
% 11.53/1.85  fof(f8678,plain,(
% 11.53/1.85    spl4_599 <=> sK1 = k1_relat_1(sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_599])])).
% 11.53/1.85  fof(f8348,plain,(
% 11.53/1.85    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52 | ~spl4_53 | ~spl4_570)),
% 11.53/1.85    inference(trivial_inequality_removal,[],[f8347])).
% 11.53/1.85  fof(f8347,plain,(
% 11.53/1.85    k6_relat_1(sK0) != k6_relat_1(sK0) | sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52 | ~spl4_53 | ~spl4_570)),
% 11.53/1.85    inference(forward_demodulation,[],[f8346,f1538])).
% 11.53/1.85  fof(f1538,plain,(
% 11.53/1.85    sK0 = k2_relat_1(sK3) | ~spl4_53),
% 11.53/1.85    inference(avatar_component_clause,[],[f608])).
% 11.53/1.85  fof(f608,plain,(
% 11.53/1.85    spl4_53 <=> sK0 = k2_relat_1(sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 11.53/1.85  fof(f8346,plain,(
% 11.53/1.85    k6_relat_1(sK0) != k6_relat_1(k2_relat_1(sK3)) | sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52 | ~spl4_570)),
% 11.53/1.85    inference(forward_demodulation,[],[f8345,f7960])).
% 11.53/1.85  fof(f7960,plain,(
% 11.53/1.85    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_570),
% 11.53/1.85    inference(avatar_component_clause,[],[f7959])).
% 11.53/1.85  fof(f7959,plain,(
% 11.53/1.85    spl4_570 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_570])])).
% 11.53/1.85  fof(f8345,plain,(
% 11.53/1.85    sK1 != k1_relat_1(sK3) | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_10 | ~spl4_12 | ~spl4_15 | ~spl4_52)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8344,f211])).
% 11.53/1.85  fof(f211,plain,(
% 11.53/1.85    v1_relat_1(sK3) | ~spl4_10),
% 11.53/1.85    inference(avatar_component_clause,[],[f154])).
% 11.53/1.85  fof(f154,plain,(
% 11.53/1.85    spl4_10 <=> v1_relat_1(sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 11.53/1.85  fof(f8344,plain,(
% 11.53/1.85    ~v1_relat_1(sK3) | sK1 != k1_relat_1(sK3) | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_12 | ~spl4_15 | ~spl4_52)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8329,f102])).
% 11.53/1.85  fof(f102,plain,(
% 11.53/1.85    v1_funct_1(sK3) | ~spl4_1),
% 11.53/1.85    inference(avatar_component_clause,[],[f101])).
% 11.53/1.85  fof(f101,plain,(
% 11.53/1.85    spl4_1 <=> v1_funct_1(sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 11.53/1.85  fof(f8329,plain,(
% 11.53/1.85    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK1 != k1_relat_1(sK3) | k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | sK2 = k2_funct_1(sK3) | (~spl4_3 | ~spl4_12 | ~spl4_15 | ~spl4_52)),
% 11.53/1.85    inference(resolution,[],[f8315,f267])).
% 11.53/1.85  fof(f267,plain,(
% 11.53/1.85    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) != sK1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k2_funct_1(X0) = sK2) ) | (~spl4_3 | ~spl4_12 | ~spl4_15)),
% 11.53/1.85    inference(forward_demodulation,[],[f266,f252])).
% 11.53/1.85  fof(f252,plain,(
% 11.53/1.85    sK1 = k2_relat_1(sK2) | (~spl4_12 | ~spl4_15)),
% 11.53/1.85    inference(forward_demodulation,[],[f222,f163])).
% 11.53/1.85  fof(f163,plain,(
% 11.53/1.85    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_12),
% 11.53/1.85    inference(avatar_component_clause,[],[f162])).
% 11.53/1.85  fof(f162,plain,(
% 11.53/1.85    spl4_12 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 11.53/1.85  fof(f222,plain,(
% 11.53/1.85    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) | ~spl4_15),
% 11.53/1.85    inference(resolution,[],[f174,f89])).
% 11.53/1.85  fof(f89,plain,(
% 11.53/1.85    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 11.53/1.85    inference(cnf_transformation,[],[f48])).
% 11.53/1.85  fof(f48,plain,(
% 11.53/1.85    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.85    inference(ennf_transformation,[],[f9])).
% 11.53/1.85  fof(f9,axiom,(
% 11.53/1.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 11.53/1.85  fof(f174,plain,(
% 11.53/1.85    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_15),
% 11.53/1.85    inference(avatar_component_clause,[],[f173])).
% 11.53/1.85  fof(f173,plain,(
% 11.53/1.85    spl4_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 11.53/1.85  fof(f266,plain,(
% 11.53/1.85    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k2_funct_1(X0) = sK2) ) | (~spl4_3 | ~spl4_15)),
% 11.53/1.85    inference(subsumption_resolution,[],[f129,f223])).
% 11.53/1.85  fof(f223,plain,(
% 11.53/1.85    v1_relat_1(sK2) | ~spl4_15),
% 11.53/1.85    inference(resolution,[],[f174,f90])).
% 11.53/1.85  fof(f90,plain,(
% 11.53/1.85    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 11.53/1.85    inference(cnf_transformation,[],[f49])).
% 11.53/1.85  fof(f49,plain,(
% 11.53/1.85    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.85    inference(ennf_transformation,[],[f7])).
% 11.53/1.85  fof(f7,axiom,(
% 11.53/1.85    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 11.53/1.85  fof(f129,plain,(
% 11.53/1.85    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK2) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k2_funct_1(X0) = sK2) ) | ~spl4_3),
% 11.53/1.85    inference(resolution,[],[f110,f67])).
% 11.53/1.85  fof(f67,plain,(
% 11.53/1.85    ( ! [X0,X1] : (~v1_funct_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 11.53/1.85    inference(cnf_transformation,[],[f27])).
% 11.53/1.85  fof(f27,plain,(
% 11.53/1.85    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.85    inference(flattening,[],[f26])).
% 11.53/1.85  fof(f26,plain,(
% 11.53/1.85    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.85    inference(ennf_transformation,[],[f6])).
% 11.53/1.85  fof(f6,axiom,(
% 11.53/1.85    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 11.53/1.85  fof(f110,plain,(
% 11.53/1.85    v1_funct_1(sK2) | ~spl4_3),
% 11.53/1.85    inference(avatar_component_clause,[],[f109])).
% 11.53/1.85  fof(f109,plain,(
% 11.53/1.85    spl4_3 <=> v1_funct_1(sK2)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 11.53/1.85  fof(f8315,plain,(
% 11.53/1.85    v2_funct_1(sK3) | ~spl4_52),
% 11.53/1.85    inference(avatar_component_clause,[],[f600])).
% 11.53/1.85  fof(f600,plain,(
% 11.53/1.85    spl4_52 <=> v2_funct_1(sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 11.53/1.85  fof(f7364,plain,(
% 11.53/1.85    k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | spl4_560),
% 11.53/1.85    inference(avatar_component_clause,[],[f7363])).
% 11.53/1.85  fof(f7363,plain,(
% 11.53/1.85    spl4_560 <=> k6_relat_1(sK0) = k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_560])])).
% 11.53/1.85  fof(f9361,plain,(
% 11.53/1.85    k1_relat_1(sK3) != k2_relat_1(k2_funct_1(sK3)) | k1_relat_1(sK3) != k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | sK1 = k2_relat_1(k2_funct_1(sK3))),
% 11.53/1.85    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.85  fof(f9360,plain,(
% 11.53/1.85    k1_relat_1(sK3) != k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 11.53/1.85    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.85  fof(f9359,plain,(
% 11.53/1.85    k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3)) | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(sK1) | r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1)) | ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3)))),
% 11.53/1.85    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.85  fof(f9358,plain,(
% 11.53/1.85    spl4_618 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_570),
% 11.53/1.85    inference(avatar_split_clause,[],[f8278,f7959,f2260,f1638,f1540,f1428,f173,f162,f158,f147,f139,f131,f109,f101,f9356])).
% 11.53/1.85  fof(f9356,plain,(
% 11.53/1.85    spl4_618 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_618])])).
% 11.53/1.85  fof(f131,plain,(
% 11.53/1.85    spl4_4 <=> k1_xboole_0 = sK0),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 11.53/1.85  fof(f139,plain,(
% 11.53/1.85    spl4_6 <=> v1_funct_2(sK3,sK1,sK0)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 11.53/1.85  fof(f147,plain,(
% 11.53/1.85    spl4_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 11.53/1.85  fof(f158,plain,(
% 11.53/1.85    spl4_11 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 11.53/1.85  fof(f1428,plain,(
% 11.53/1.85    spl4_113 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_113])])).
% 11.53/1.85  fof(f1540,plain,(
% 11.53/1.85    spl4_119 <=> sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_119])])).
% 11.53/1.85  fof(f1638,plain,(
% 11.53/1.85    spl4_131 <=> v1_funct_2(sK3,k1_relat_1(sK3),sK0)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_131])])).
% 11.53/1.85  fof(f2260,plain,(
% 11.53/1.85    spl4_164 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_164])])).
% 11.53/1.85  fof(f8278,plain,(
% 11.53/1.85    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_570)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8246,f8273])).
% 11.53/1.85  fof(f8273,plain,(
% 11.53/1.85    v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113 | ~spl4_570)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8272,f94])).
% 11.53/1.85  fof(f94,plain,(
% 11.53/1.85    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 11.53/1.85    inference(cnf_transformation,[],[f2])).
% 11.53/1.85  fof(f2,axiom,(
% 11.53/1.85    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 11.53/1.85  fof(f8272,plain,(
% 11.53/1.85    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113 | ~spl4_570)),
% 11.53/1.85    inference(forward_demodulation,[],[f1525,f7960])).
% 11.53/1.85  fof(f1525,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1524,f132])).
% 11.53/1.85  fof(f132,plain,(
% 11.53/1.85    k1_xboole_0 != sK0 | spl4_4),
% 11.53/1.85    inference(avatar_component_clause,[],[f131])).
% 11.53/1.85  fof(f1524,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1523,f163])).
% 11.53/1.85  fof(f1523,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1522,f110])).
% 11.53/1.85  fof(f1522,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1521,f159])).
% 11.53/1.85  fof(f159,plain,(
% 11.53/1.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_11),
% 11.53/1.85    inference(avatar_component_clause,[],[f158])).
% 11.53/1.85  fof(f1521,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_1 | ~spl4_6 | ~spl4_8 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1520,f140])).
% 11.53/1.85  fof(f140,plain,(
% 11.53/1.85    v1_funct_2(sK3,sK1,sK0) | ~spl4_6),
% 11.53/1.85    inference(avatar_component_clause,[],[f139])).
% 11.53/1.85  fof(f1520,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_1 | ~spl4_8 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1519,f102])).
% 11.53/1.85  fof(f1519,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_8 | ~spl4_15 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1518,f174])).
% 11.53/1.85  fof(f1518,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | (~spl4_8 | ~spl4_113)),
% 11.53/1.85    inference(subsumption_resolution,[],[f1516,f148])).
% 11.53/1.85  fof(f148,plain,(
% 11.53/1.85    v1_funct_2(sK2,sK0,sK1) | ~spl4_8),
% 11.53/1.85    inference(avatar_component_clause,[],[f147])).
% 11.53/1.85  fof(f1516,plain,(
% 11.53/1.85    ~v2_funct_1(k5_relat_1(sK2,sK3)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK0 | v2_funct_1(sK3) | ~spl4_113),
% 11.53/1.85    inference(superposition,[],[f77,f1429])).
% 11.53/1.85  fof(f1429,plain,(
% 11.53/1.85    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~spl4_113),
% 11.53/1.85    inference(avatar_component_clause,[],[f1428])).
% 11.53/1.85  fof(f77,plain,(
% 11.53/1.85    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X3) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 11.53/1.85    inference(cnf_transformation,[],[f35])).
% 11.53/1.85  fof(f35,plain,(
% 11.53/1.85    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.53/1.85    inference(flattening,[],[f34])).
% 11.53/1.85  fof(f34,plain,(
% 11.53/1.85    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.53/1.85    inference(ennf_transformation,[],[f16])).
% 11.53/1.85  fof(f16,axiom,(
% 11.53/1.85    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 11.53/1.85  fof(f8246,plain,(
% 11.53/1.85    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | (~spl4_1 | spl4_4 | ~spl4_119 | ~spl4_131 | ~spl4_164)),
% 11.53/1.85    inference(forward_demodulation,[],[f8245,f85])).
% 11.53/1.85  fof(f85,plain,(
% 11.53/1.85    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.53/1.85    inference(cnf_transformation,[],[f14])).
% 11.53/1.85  fof(f14,axiom,(
% 11.53/1.85    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 11.53/1.85  fof(f8245,plain,(
% 11.53/1.85    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_1 | spl4_4 | ~spl4_119 | ~spl4_131 | ~spl4_164)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8244,f132])).
% 11.53/1.85  fof(f8244,plain,(
% 11.53/1.85    ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_1 | ~spl4_119 | ~spl4_131 | ~spl4_164)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8243,f1541])).
% 11.53/1.85  fof(f1541,plain,(
% 11.53/1.85    sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~spl4_119),
% 11.53/1.85    inference(avatar_component_clause,[],[f1540])).
% 11.53/1.85  fof(f8243,plain,(
% 11.53/1.85    sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_1 | ~spl4_131 | ~spl4_164)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8242,f102])).
% 11.53/1.85  fof(f8242,plain,(
% 11.53/1.85    ~v1_funct_1(sK3) | sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | (~spl4_131 | ~spl4_164)),
% 11.53/1.85    inference(subsumption_resolution,[],[f2411,f1639])).
% 11.53/1.85  fof(f1639,plain,(
% 11.53/1.85    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~spl4_131),
% 11.53/1.85    inference(avatar_component_clause,[],[f1638])).
% 11.53/1.85  fof(f2411,plain,(
% 11.53/1.85    ~v1_funct_2(sK3,k1_relat_1(sK3),sK0) | ~v1_funct_1(sK3) | sK0 != k2_relset_1(k1_relat_1(sK3),sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) | ~spl4_164),
% 11.53/1.85    inference(resolution,[],[f2261,f78])).
% 11.53/1.85  fof(f78,plain,(
% 11.53/1.85    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 11.53/1.85    inference(cnf_transformation,[],[f37])).
% 11.53/1.85  fof(f37,plain,(
% 11.53/1.85    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.53/1.85    inference(flattening,[],[f36])).
% 11.53/1.85  fof(f36,plain,(
% 11.53/1.85    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.53/1.85    inference(ennf_transformation,[],[f18])).
% 11.53/1.85  fof(f18,axiom,(
% 11.53/1.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 11.53/1.85  fof(f2261,plain,(
% 11.53/1.85    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | ~spl4_164),
% 11.53/1.85    inference(avatar_component_clause,[],[f2260])).
% 11.53/1.85  fof(f9354,plain,(
% 11.53/1.85    spl4_617 | ~spl4_601),
% 11.53/1.85    inference(avatar_split_clause,[],[f8718,f8687,f9352])).
% 11.53/1.85  fof(f9352,plain,(
% 11.53/1.85    spl4_617 <=> r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_617])])).
% 11.53/1.85  fof(f8687,plain,(
% 11.53/1.85    spl4_601 <=> m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_601])])).
% 11.53/1.85  fof(f8718,plain,(
% 11.53/1.85    r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(k1_relat_1(sK3))) | ~spl4_601),
% 11.53/1.85    inference(resolution,[],[f8688,f98])).
% 11.53/1.85  fof(f98,plain,(
% 11.53/1.85    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 11.53/1.85    inference(duplicate_literal_removal,[],[f97])).
% 11.53/1.85  fof(f97,plain,(
% 11.53/1.85    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r2_relset_1(X0,X1,X3,X3)) )),
% 11.53/1.85    inference(equality_resolution,[],[f82])).
% 11.53/1.85  fof(f82,plain,(
% 11.53/1.85    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 != X3 | r2_relset_1(X0,X1,X2,X3)) )),
% 11.53/1.85    inference(cnf_transformation,[],[f41])).
% 11.53/1.85  fof(f41,plain,(
% 11.53/1.85    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.53/1.85    inference(flattening,[],[f40])).
% 11.53/1.85  fof(f40,plain,(
% 11.53/1.85    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.53/1.85    inference(ennf_transformation,[],[f10])).
% 11.53/1.85  fof(f10,axiom,(
% 11.53/1.85    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 11.53/1.85  fof(f8688,plain,(
% 11.53/1.85    m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~spl4_601),
% 11.53/1.85    inference(avatar_component_clause,[],[f8687])).
% 11.53/1.85  fof(f9316,plain,(
% 11.53/1.85    ~spl4_611 | ~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_50 | ~spl4_575 | ~spl4_582 | ~spl4_590 | spl4_597),
% 11.53/1.85    inference(avatar_split_clause,[],[f8676,f8668,f8632,f8561,f8354,f594,f275,f158,f139,f101,f9314])).
% 11.53/1.85  fof(f9314,plain,(
% 11.53/1.85    spl4_611 <=> r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_611])])).
% 11.53/1.85  fof(f275,plain,(
% 11.53/1.85    spl4_17 <=> v1_funct_1(k2_funct_1(sK3))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 11.53/1.85  fof(f594,plain,(
% 11.53/1.85    spl4_50 <=> v1_funct_2(k2_funct_1(sK3),sK0,sK1)),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 11.53/1.85  fof(f8354,plain,(
% 11.53/1.85    spl4_575 <=> m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_575])])).
% 11.53/1.85  fof(f8561,plain,(
% 11.53/1.85    spl4_582 <=> k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_582])])).
% 11.53/1.85  fof(f8632,plain,(
% 11.53/1.85    spl4_590 <=> k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_590])])).
% 11.53/1.85  fof(f8668,plain,(
% 11.53/1.85    spl4_597 <=> sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_597])])).
% 11.53/1.85  fof(f8676,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1)) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_50 | ~spl4_575 | ~spl4_582 | ~spl4_590 | spl4_597)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8659,f8675])).
% 11.53/1.85  fof(f8675,plain,(
% 11.53/1.85    sK1 != k1_relat_1(sK3) | (~spl4_582 | spl4_597)),
% 11.53/1.85    inference(superposition,[],[f8669,f8562])).
% 11.53/1.85  fof(f8562,plain,(
% 11.53/1.85    k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | ~spl4_582),
% 11.53/1.85    inference(avatar_component_clause,[],[f8561])).
% 11.53/1.85  fof(f8669,plain,(
% 11.53/1.85    sK1 != k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | spl4_597),
% 11.53/1.85    inference(avatar_component_clause,[],[f8668])).
% 11.53/1.85  fof(f8659,plain,(
% 11.53/1.85    sK1 = k1_relat_1(sK3) | ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1)) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_50 | ~spl4_575 | ~spl4_582 | ~spl4_590)),
% 11.53/1.85    inference(forward_demodulation,[],[f8658,f8562])).
% 11.53/1.85  fof(f8658,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_relat_1(sK1)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(forward_demodulation,[],[f8657,f85])).
% 11.53/1.85  fof(f8657,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_17 | ~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8656,f276])).
% 11.53/1.85  fof(f276,plain,(
% 11.53/1.85    v1_funct_1(k2_funct_1(sK3)) | ~spl4_17),
% 11.53/1.85    inference(avatar_component_clause,[],[f275])).
% 11.53/1.85  fof(f8656,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8655,f159])).
% 11.53/1.85  fof(f8655,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8654,f140])).
% 11.53/1.85  fof(f8654,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8653,f102])).
% 11.53/1.85  fof(f8653,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_50 | ~spl4_575 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8652,f8355])).
% 11.53/1.85  fof(f8355,plain,(
% 11.53/1.85    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_575),
% 11.53/1.85    inference(avatar_component_clause,[],[f8354])).
% 11.53/1.85  fof(f8652,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_50 | ~spl4_590)),
% 11.53/1.85    inference(subsumption_resolution,[],[f8651,f595])).
% 11.53/1.85  fof(f595,plain,(
% 11.53/1.85    v1_funct_2(k2_funct_1(sK3),sK0,sK1) | ~spl4_50),
% 11.53/1.85    inference(avatar_component_clause,[],[f594])).
% 11.53/1.85  fof(f8651,plain,(
% 11.53/1.85    ~r2_relset_1(sK1,sK1,k6_relat_1(k1_relat_1(sK3)),k6_partfun1(sK1)) | ~v1_funct_2(k2_funct_1(sK3),sK0,sK1) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK3)) | sK1 = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | ~spl4_590),
% 11.53/1.85    inference(superposition,[],[f84,f8633])).
% 11.53/1.85  fof(f8633,plain,(
% 11.53/1.85    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) | ~spl4_590),
% 11.53/1.85    inference(avatar_component_clause,[],[f8632])).
% 11.53/1.85  fof(f84,plain,(
% 11.53/1.85    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 11.53/1.85    inference(cnf_transformation,[],[f43])).
% 11.53/1.85  fof(f43,plain,(
% 11.53/1.85    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.53/1.85    inference(flattening,[],[f42])).
% 11.53/1.85  fof(f42,plain,(
% 11.53/1.85    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.53/1.85    inference(ennf_transformation,[],[f15])).
% 11.53/1.85  fof(f15,axiom,(
% 11.53/1.85    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 11.53/1.85    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 11.53/1.85  fof(f8689,plain,(
% 11.53/1.85    spl4_601 | ~spl4_590 | ~spl4_600),
% 11.53/1.85    inference(avatar_split_clause,[],[f8685,f8682,f8632,f8687])).
% 11.53/1.85  fof(f8682,plain,(
% 11.53/1.85    spl4_600 <=> m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 11.53/1.85    introduced(avatar_definition,[new_symbols(naming,[spl4_600])])).
% 11.53/1.85  fof(f8685,plain,(
% 11.53/1.85    m1_subset_1(k6_relat_1(k1_relat_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | (~spl4_590 | ~spl4_600)),
% 11.53/1.85    inference(forward_demodulation,[],[f8683,f8633])).
% 11.53/1.85  fof(f8683,plain,(
% 11.53/1.85    m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~spl4_600),
% 11.53/1.85    inference(avatar_component_clause,[],[f8682])).
% 11.53/1.86  fof(f8684,plain,(
% 11.53/1.86    spl4_600 | ~spl4_1 | ~spl4_11 | ~spl4_17 | ~spl4_575),
% 11.53/1.86    inference(avatar_split_clause,[],[f8468,f8354,f275,f158,f101,f8682])).
% 11.53/1.86  fof(f8468,plain,(
% 11.53/1.86    m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | (~spl4_1 | ~spl4_11 | ~spl4_17 | ~spl4_575)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8428,f276])).
% 11.53/1.86  fof(f8428,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK3)) | m1_subset_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | (~spl4_1 | ~spl4_11 | ~spl4_575)),
% 11.53/1.86    inference(resolution,[],[f8355,f203])).
% 11.53/1.86  fof(f203,plain,(
% 11.53/1.86    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | m1_subset_1(k1_partfun1(sK1,sK0,X5,X6,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f183,f102])).
% 11.53/1.86  fof(f183,plain,(
% 11.53/1.86    ( ! [X6,X4,X5] : (~v1_funct_1(sK3) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | m1_subset_1(k1_partfun1(sK1,sK0,X5,X6,sK3,X4),k1_zfmisc_1(k2_zfmisc_1(sK1,X6)))) ) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f87])).
% 11.53/1.86  fof(f87,plain,(
% 11.53/1.86    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f45])).
% 11.53/1.86  fof(f45,plain,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.53/1.86    inference(flattening,[],[f44])).
% 11.53/1.86  fof(f44,plain,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.53/1.86    inference(ennf_transformation,[],[f12])).
% 11.53/1.86  fof(f12,axiom,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 11.53/1.86  fof(f8638,plain,(
% 11.53/1.86    spl4_591 | ~spl4_1 | ~spl4_10 | ~spl4_52),
% 11.53/1.86    inference(avatar_split_clause,[],[f8339,f600,f154,f101,f8636])).
% 11.53/1.86  fof(f8636,plain,(
% 11.53/1.86    spl4_591 <=> k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_591])])).
% 11.53/1.86  fof(f8339,plain,(
% 11.53/1.86    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_10 | ~spl4_52)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8338,f211])).
% 11.53/1.86  fof(f8338,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_52)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8327,f102])).
% 11.53/1.86  fof(f8327,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~spl4_52),
% 11.53/1.86    inference(resolution,[],[f8315,f71])).
% 11.53/1.86  fof(f71,plain,(
% 11.53/1.86    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f31])).
% 11.53/1.86  fof(f31,plain,(
% 11.53/1.86    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.86    inference(flattening,[],[f30])).
% 11.53/1.86  fof(f30,plain,(
% 11.53/1.86    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.86    inference(ennf_transformation,[],[f4])).
% 11.53/1.86  fof(f4,axiom,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 11.53/1.86  fof(f8634,plain,(
% 11.53/1.86    spl4_590 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_17 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_570 | ~spl4_575),
% 11.53/1.86    inference(avatar_split_clause,[],[f8470,f8354,f7959,f2260,f1638,f1540,f1428,f275,f173,f162,f158,f147,f139,f131,f109,f101,f8632])).
% 11.53/1.86  fof(f8470,plain,(
% 11.53/1.86    k6_relat_1(k1_relat_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_17 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_570 | ~spl4_575)),
% 11.53/1.86    inference(forward_demodulation,[],[f8469,f8278])).
% 11.53/1.86  fof(f8469,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_11 | ~spl4_17 | ~spl4_575)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8429,f276])).
% 11.53/1.86  fof(f8429,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK3)) | k5_relat_1(sK3,k2_funct_1(sK3)) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_11 | ~spl4_575)),
% 11.53/1.86    inference(resolution,[],[f8355,f204])).
% 11.53/1.86  fof(f204,plain,(
% 11.53/1.86    ( ! [X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X7) | k1_partfun1(sK1,sK0,X8,X9,sK3,X7) = k5_relat_1(sK3,X7)) ) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f184,f102])).
% 11.53/1.86  fof(f184,plain,(
% 11.53/1.86    ( ! [X8,X7,X9] : (~v1_funct_1(sK3) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_partfun1(sK1,sK0,X8,X9,sK3,X7) = k5_relat_1(sK3,X7)) ) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f88])).
% 11.53/1.86  fof(f88,plain,(
% 11.53/1.86    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 11.53/1.86    inference(cnf_transformation,[],[f47])).
% 11.53/1.86  fof(f47,plain,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.53/1.86    inference(flattening,[],[f46])).
% 11.53/1.86  fof(f46,plain,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.53/1.86    inference(ennf_transformation,[],[f13])).
% 11.53/1.86  fof(f13,axiom,(
% 11.53/1.86    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 11.53/1.86  fof(f8563,plain,(
% 11.53/1.86    spl4_582 | ~spl4_1 | ~spl4_10 | ~spl4_52 | ~spl4_575),
% 11.53/1.86    inference(avatar_split_clause,[],[f8466,f8354,f600,f154,f101,f8561])).
% 11.53/1.86  fof(f8466,plain,(
% 11.53/1.86    k1_relat_1(sK3) = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_10 | ~spl4_52 | ~spl4_575)),
% 11.53/1.86    inference(forward_demodulation,[],[f8424,f8339])).
% 11.53/1.86  fof(f8424,plain,(
% 11.53/1.86    k2_relat_1(k2_funct_1(sK3)) = k2_relset_1(sK0,sK1,k2_funct_1(sK3)) | ~spl4_575),
% 11.53/1.86    inference(resolution,[],[f8355,f89])).
% 11.53/1.86  fof(f8547,plain,(
% 11.53/1.86    k2_relat_1(sK3) != k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | sK0 = k2_relset_1(k1_relat_1(sK3),sK0,sK3)),
% 11.53/1.86    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.86  fof(f8546,plain,(
% 11.53/1.86    spl4_581 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_17 | ~spl4_52 | ~spl4_53 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_384 | ~spl4_570 | ~spl4_576),
% 11.53/1.86    inference(avatar_split_clause,[],[f8521,f8360,f7959,f4788,f2260,f1638,f1540,f1428,f608,f600,f275,f173,f162,f158,f154,f151,f147,f139,f131,f109,f101,f8544])).
% 11.53/1.86  fof(f8544,plain,(
% 11.53/1.86    spl4_581 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_581])])).
% 11.53/1.86  fof(f151,plain,(
% 11.53/1.86    spl4_9 <=> v1_relat_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 11.53/1.86  fof(f4788,plain,(
% 11.53/1.86    spl4_384 <=> v2_funct_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_384])])).
% 11.53/1.86  fof(f8360,plain,(
% 11.53/1.86    spl4_576 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_576])])).
% 11.53/1.86  fof(f8521,plain,(
% 11.53/1.86    sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_17 | ~spl4_52 | ~spl4_53 | ~spl4_113 | ~spl4_119 | ~spl4_131 | ~spl4_164 | ~spl4_384 | ~spl4_570 | ~spl4_576)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8520,f8278])).
% 11.53/1.86  fof(f8520,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k1_relat_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_17 | ~spl4_52 | ~spl4_53 | ~spl4_384 | ~spl4_576)),
% 11.53/1.86    inference(forward_demodulation,[],[f8519,f8339])).
% 11.53/1.86  fof(f8519,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_11 | ~spl4_17 | ~spl4_53 | ~spl4_384 | ~spl4_576)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8518,f1538])).
% 11.53/1.86  fof(f8518,plain,(
% 11.53/1.86    sK0 != k2_relat_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_11 | ~spl4_17 | ~spl4_384 | ~spl4_576)),
% 11.53/1.86    inference(forward_demodulation,[],[f8517,f8361])).
% 11.53/1.86  fof(f8361,plain,(
% 11.53/1.86    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~spl4_576),
% 11.53/1.86    inference(avatar_component_clause,[],[f8360])).
% 11.53/1.86  fof(f8517,plain,(
% 11.53/1.86    k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_11 | ~spl4_17 | ~spl4_384)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8516,f276])).
% 11.53/1.86  fof(f8516,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_11 | ~spl4_384)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8500,f152])).
% 11.53/1.86  fof(f152,plain,(
% 11.53/1.86    v1_relat_1(k2_funct_1(sK3)) | ~spl4_9),
% 11.53/1.86    inference(avatar_component_clause,[],[f151])).
% 11.53/1.86  fof(f8500,plain,(
% 11.53/1.86    ~v1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | k5_relat_1(sK3,k2_funct_1(sK3)) != k6_relat_1(k2_relat_1(k2_funct_1(sK3))) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_11 | ~spl4_384)),
% 11.53/1.86    inference(resolution,[],[f8412,f207])).
% 11.53/1.86  fof(f207,plain,(
% 11.53/1.86    ( ! [X0] : (~v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK3,X0) | k2_funct_1(X0) = sK3) ) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f116,f186])).
% 11.53/1.86  fof(f186,plain,(
% 11.53/1.86    v1_relat_1(sK3) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f90])).
% 11.53/1.86  fof(f116,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(sK3) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK3,X0) | k2_funct_1(X0) = sK3) ) | ~spl4_1),
% 11.53/1.86    inference(resolution,[],[f102,f67])).
% 11.53/1.86  fof(f8412,plain,(
% 11.53/1.86    v2_funct_1(k2_funct_1(sK3)) | ~spl4_384),
% 11.53/1.86    inference(avatar_component_clause,[],[f4788])).
% 11.53/1.86  fof(f8413,plain,(
% 11.53/1.86    spl4_384 | ~spl4_1 | ~spl4_9 | ~spl4_10 | ~spl4_17 | ~spl4_53 | ~spl4_573 | ~spl4_576),
% 11.53/1.86    inference(avatar_split_clause,[],[f8397,f8360,f8318,f608,f275,f154,f151,f101,f4788])).
% 11.53/1.86  fof(f8318,plain,(
% 11.53/1.86    spl4_573 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_573])])).
% 11.53/1.86  fof(f8397,plain,(
% 11.53/1.86    v2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_10 | ~spl4_17 | ~spl4_53 | ~spl4_573 | ~spl4_576)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8396,f1538])).
% 11.53/1.86  fof(f8396,plain,(
% 11.53/1.86    sK0 != k2_relat_1(sK3) | v2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_10 | ~spl4_17 | ~spl4_573 | ~spl4_576)),
% 11.53/1.86    inference(forward_demodulation,[],[f8391,f8361])).
% 11.53/1.86  fof(f8391,plain,(
% 11.53/1.86    k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_9 | ~spl4_10 | ~spl4_17 | ~spl4_573)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8390,f152])).
% 11.53/1.86  fof(f8390,plain,(
% 11.53/1.86    ~v1_relat_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_10 | ~spl4_17 | ~spl4_573)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8389,f102])).
% 11.53/1.86  fof(f8389,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | (~spl4_10 | ~spl4_17 | ~spl4_573)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8388,f211])).
% 11.53/1.86  fof(f8388,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | (~spl4_17 | ~spl4_573)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8387,f276])).
% 11.53/1.86  fof(f8387,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | ~spl4_573),
% 11.53/1.86    inference(subsumption_resolution,[],[f8385,f94])).
% 11.53/1.86  fof(f8385,plain,(
% 11.53/1.86    ~v2_funct_1(k6_relat_1(sK1)) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | v2_funct_1(k2_funct_1(sK3)) | ~spl4_573),
% 11.53/1.86    inference(superposition,[],[f81,f8319])).
% 11.53/1.86  fof(f8319,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) | ~spl4_573),
% 11.53/1.86    inference(avatar_component_clause,[],[f8318])).
% 11.53/1.86  fof(f81,plain,(
% 11.53/1.86    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0)) )),
% 11.53/1.86    inference(cnf_transformation,[],[f39])).
% 11.53/1.86  fof(f39,plain,(
% 11.53/1.86    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.86    inference(flattening,[],[f38])).
% 11.53/1.86  fof(f38,plain,(
% 11.53/1.86    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.86    inference(ennf_transformation,[],[f3])).
% 11.53/1.86  fof(f3,axiom,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_1)).
% 11.53/1.86  fof(f8362,plain,(
% 11.53/1.86    spl4_576 | ~spl4_1 | ~spl4_10 | ~spl4_52 | ~spl4_53),
% 11.53/1.86    inference(avatar_split_clause,[],[f8337,f608,f600,f154,f101,f8360])).
% 11.53/1.86  fof(f8337,plain,(
% 11.53/1.86    sK0 = k1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_10 | ~spl4_52 | ~spl4_53)),
% 11.53/1.86    inference(forward_demodulation,[],[f8336,f1538])).
% 11.53/1.86  fof(f8336,plain,(
% 11.53/1.86    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_10 | ~spl4_52)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8335,f211])).
% 11.53/1.86  fof(f8335,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_52)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8326,f102])).
% 11.53/1.86  fof(f8326,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~spl4_52),
% 11.53/1.86    inference(resolution,[],[f8315,f70])).
% 11.53/1.86  fof(f70,plain,(
% 11.53/1.86    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f31])).
% 11.53/1.86  fof(f8356,plain,(
% 11.53/1.86    spl4_575 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_51 | ~spl4_113 | ~spl4_570),
% 11.53/1.86    inference(avatar_split_clause,[],[f8275,f7959,f1428,f597,f173,f162,f158,f147,f139,f131,f109,f101,f8354])).
% 11.53/1.86  fof(f597,plain,(
% 11.53/1.86    spl4_51 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 11.53/1.86  fof(f8275,plain,(
% 11.53/1.86    m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_51 | ~spl4_113 | ~spl4_570)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8253,f8273])).
% 11.53/1.86  fof(f8253,plain,(
% 11.53/1.86    ~v2_funct_1(sK3) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_1 | ~spl4_6 | ~spl4_11 | ~spl4_51)),
% 11.53/1.86    inference(subsumption_resolution,[],[f193,f1542])).
% 11.53/1.86  fof(f1542,plain,(
% 11.53/1.86    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_51),
% 11.53/1.86    inference(avatar_component_clause,[],[f597])).
% 11.53/1.86  fof(f193,plain,(
% 11.53/1.86    ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_1 | ~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f192,f102])).
% 11.53/1.86  fof(f192,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f178,f140])).
% 11.53/1.86  fof(f178,plain,(
% 11.53/1.86    ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f66])).
% 11.53/1.86  fof(f66,plain,(
% 11.53/1.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f25])).
% 11.53/1.86  fof(f25,plain,(
% 11.53/1.86    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.53/1.86    inference(flattening,[],[f24])).
% 11.53/1.86  fof(f24,plain,(
% 11.53/1.86    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.53/1.86    inference(ennf_transformation,[],[f17])).
% 11.53/1.86  fof(f17,axiom,(
% 11.53/1.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 11.53/1.86  fof(f8320,plain,(
% 11.53/1.86    spl4_573 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_51 | ~spl4_113 | ~spl4_570),
% 11.53/1.86    inference(avatar_split_clause,[],[f8274,f7959,f1428,f597,f173,f162,f158,f147,f139,f131,f109,f101,f8318])).
% 11.53/1.86  fof(f8274,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) | (~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_51 | ~spl4_113 | ~spl4_570)),
% 11.53/1.86    inference(subsumption_resolution,[],[f8254,f8273])).
% 11.53/1.86  fof(f8254,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) | ~v2_funct_1(sK3) | (~spl4_1 | spl4_4 | ~spl4_6 | ~spl4_11 | ~spl4_51)),
% 11.53/1.86    inference(subsumption_resolution,[],[f197,f1542])).
% 11.53/1.86  fof(f197,plain,(
% 11.53/1.86    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | (~spl4_1 | spl4_4 | ~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(forward_demodulation,[],[f196,f85])).
% 11.53/1.86  fof(f196,plain,(
% 11.53/1.86    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (~spl4_1 | spl4_4 | ~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f195,f132])).
% 11.53/1.86  fof(f195,plain,(
% 11.53/1.86    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (~spl4_1 | ~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f194,f102])).
% 11.53/1.86  fof(f194,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f179,f140])).
% 11.53/1.86  fof(f179,plain,(
% 11.53/1.86    ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f78])).
% 11.53/1.86  fof(f8316,plain,(
% 11.53/1.86    spl4_52 | ~spl4_1 | ~spl4_3 | spl4_4 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_12 | ~spl4_15 | ~spl4_113 | ~spl4_570),
% 11.53/1.86    inference(avatar_split_clause,[],[f8273,f7959,f1428,f173,f162,f158,f147,f139,f131,f109,f101,f600])).
% 11.53/1.86  fof(f7961,plain,(
% 11.53/1.86    spl4_570 | ~spl4_59 | ~spl4_76 | ~spl4_150),
% 11.53/1.86    inference(avatar_split_clause,[],[f7957,f2150,f897,f768,f7959])).
% 11.53/1.86  fof(f768,plain,(
% 11.53/1.86    spl4_59 <=> m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 11.53/1.86  fof(f897,plain,(
% 11.53/1.86    spl4_76 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 11.53/1.86  fof(f2150,plain,(
% 11.53/1.86    spl4_150 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_150])])).
% 11.53/1.86  fof(f7957,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_59 | ~spl4_76 | ~spl4_150)),
% 11.53/1.86    inference(subsumption_resolution,[],[f7955,f769])).
% 11.53/1.86  fof(f769,plain,(
% 11.53/1.86    m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_59),
% 11.53/1.86    inference(avatar_component_clause,[],[f768])).
% 11.53/1.86  fof(f7955,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_76 | ~spl4_150)),
% 11.53/1.86    inference(resolution,[],[f1042,f2151])).
% 11.53/1.86  fof(f2151,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_150),
% 11.53/1.86    inference(avatar_component_clause,[],[f2150])).
% 11.53/1.86  fof(f1042,plain,(
% 11.53/1.86    ( ! [X0] : (~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) | k5_relat_1(sK2,sK3) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) ) | ~spl4_76),
% 11.53/1.86    inference(resolution,[],[f898,f83])).
% 11.53/1.86  fof(f83,plain,(
% 11.53/1.86    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 11.53/1.86    inference(cnf_transformation,[],[f41])).
% 11.53/1.86  fof(f898,plain,(
% 11.53/1.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_76),
% 11.53/1.86    inference(avatar_component_clause,[],[f897])).
% 11.53/1.86  fof(f7368,plain,(
% 11.53/1.86    ~spl4_559 | ~spl4_560 | spl4_561 | ~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_46 | ~spl4_55),
% 11.53/1.86    inference(avatar_split_clause,[],[f2101,f711,f503,f388,f380,f340,f279,f275,f166,f151,f7366,f7363,f7360])).
% 11.53/1.86  fof(f7360,plain,(
% 11.53/1.86    spl4_559 <=> sK1 = k2_relat_1(k2_funct_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_559])])).
% 11.53/1.86  fof(f7366,plain,(
% 11.53/1.86    spl4_561 <=> sK2 = k2_funct_1(sK3)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_561])])).
% 11.53/1.86  fof(f166,plain,(
% 11.53/1.86    spl4_13 <=> v1_relat_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 11.53/1.86  fof(f279,plain,(
% 11.53/1.86    spl4_18 <=> v1_funct_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 11.53/1.86  fof(f340,plain,(
% 11.53/1.86    spl4_27 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 11.53/1.86  fof(f380,plain,(
% 11.53/1.86    spl4_32 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 11.53/1.86  fof(f388,plain,(
% 11.53/1.86    spl4_34 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 11.53/1.86  fof(f503,plain,(
% 11.53/1.86    spl4_46 <=> v2_funct_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 11.53/1.86  fof(f711,plain,(
% 11.53/1.86    spl4_55 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 11.53/1.86  fof(f2101,plain,(
% 11.53/1.86    sK2 = k2_funct_1(sK3) | k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | sK1 != k2_relat_1(k2_funct_1(sK3)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_46 | ~spl4_55)),
% 11.53/1.86    inference(forward_demodulation,[],[f2100,f712])).
% 11.53/1.86  fof(f712,plain,(
% 11.53/1.86    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl4_55),
% 11.53/1.86    inference(avatar_component_clause,[],[f711])).
% 11.53/1.86  fof(f2100,plain,(
% 11.53/1.86    k6_relat_1(sK0) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | sK1 != k2_relat_1(k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_46)),
% 11.53/1.86    inference(forward_demodulation,[],[f2099,f389])).
% 11.53/1.86  fof(f389,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_34),
% 11.53/1.86    inference(avatar_component_clause,[],[f388])).
% 11.53/1.86  fof(f2099,plain,(
% 11.53/1.86    k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | sK1 != k2_relat_1(k2_funct_1(sK3)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_46)),
% 11.53/1.86    inference(forward_demodulation,[],[f2098,f381])).
% 11.53/1.86  fof(f381,plain,(
% 11.53/1.86    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_32),
% 11.53/1.86    inference(avatar_component_clause,[],[f380])).
% 11.53/1.86  fof(f2098,plain,(
% 11.53/1.86    sK1 != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_27 | ~spl4_46)),
% 11.53/1.86    inference(forward_demodulation,[],[f2097,f341])).
% 11.53/1.86  fof(f341,plain,(
% 11.53/1.86    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_27),
% 11.53/1.86    inference(avatar_component_clause,[],[f340])).
% 11.53/1.86  fof(f2097,plain,(
% 11.53/1.86    k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_18 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f2096,f280])).
% 11.53/1.86  fof(f280,plain,(
% 11.53/1.86    v1_funct_1(k2_funct_1(sK2)) | ~spl4_18),
% 11.53/1.86    inference(avatar_component_clause,[],[f279])).
% 11.53/1.86  fof(f2096,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_13 | ~spl4_17 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f2091,f167])).
% 11.53/1.86  fof(f167,plain,(
% 11.53/1.86    v1_relat_1(k2_funct_1(sK2)) | ~spl4_13),
% 11.53/1.86    inference(avatar_component_clause,[],[f166])).
% 11.53/1.86  fof(f2091,plain,(
% 11.53/1.86    ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k5_relat_1(k2_funct_1(sK3),k2_funct_1(sK2)) | k2_funct_1(sK3) = k2_funct_1(k2_funct_1(sK2)) | (~spl4_9 | ~spl4_17 | ~spl4_46)),
% 11.53/1.86    inference(resolution,[],[f291,f504])).
% 11.53/1.86  fof(f504,plain,(
% 11.53/1.86    v2_funct_1(k2_funct_1(sK2)) | ~spl4_46),
% 11.53/1.86    inference(avatar_component_clause,[],[f503])).
% 11.53/1.86  fof(f291,plain,(
% 11.53/1.86    ( ! [X0] : (~v2_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(k2_funct_1(sK3),X0) | k2_funct_1(X0) = k2_funct_1(sK3)) ) | (~spl4_9 | ~spl4_17)),
% 11.53/1.86    inference(subsumption_resolution,[],[f286,f152])).
% 11.53/1.86  fof(f286,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(k2_funct_1(sK3)) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(k2_funct_1(sK3),X0) | k2_funct_1(X0) = k2_funct_1(sK3)) ) | ~spl4_17),
% 11.53/1.86    inference(resolution,[],[f276,f67])).
% 11.53/1.86  fof(f2262,plain,(
% 11.53/1.86    spl4_164 | ~spl4_48 | ~spl4_53),
% 11.53/1.86    inference(avatar_split_clause,[],[f1559,f608,f557,f2260])).
% 11.53/1.86  fof(f557,plain,(
% 11.53/1.86    spl4_48 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 11.53/1.86  fof(f1559,plain,(
% 11.53/1.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) | (~spl4_48 | ~spl4_53)),
% 11.53/1.86    inference(superposition,[],[f558,f1538])).
% 11.53/1.86  fof(f558,plain,(
% 11.53/1.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_48),
% 11.53/1.86    inference(avatar_component_clause,[],[f557])).
% 11.53/1.86  fof(f2152,plain,(
% 11.53/1.86    spl4_150 | ~spl4_16 | ~spl4_113),
% 11.53/1.86    inference(avatar_split_clause,[],[f1514,f1428,f271,f2150])).
% 11.53/1.86  fof(f271,plain,(
% 11.53/1.86    spl4_16 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 11.53/1.86  fof(f1514,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_16 | ~spl4_113)),
% 11.53/1.86    inference(superposition,[],[f272,f1429])).
% 11.53/1.86  fof(f272,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_16),
% 11.53/1.86    inference(avatar_component_clause,[],[f271])).
% 11.53/1.86  fof(f2111,plain,(
% 11.53/1.86    sK0 != k2_relset_1(sK1,sK0,sK3) | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3) | k2_relat_1(sK3) != k1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 11.53/1.86    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.86  fof(f2110,plain,(
% 11.53/1.86    k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | sK0 != k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | k2_relat_1(sK3) = k1_relat_1(sK2)),
% 11.53/1.86    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.86  fof(f2109,plain,(
% 11.53/1.86    spl4_144 | ~spl4_3 | ~spl4_8 | ~spl4_15 | ~spl4_18 | ~spl4_25 | ~spl4_37 | ~spl4_62 | ~spl4_115),
% 11.53/1.86    inference(avatar_split_clause,[],[f1574,f1446,f807,f422,f332,f279,f173,f147,f109,f2107])).
% 11.53/1.86  fof(f2107,plain,(
% 11.53/1.86    spl4_144 <=> sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_144])])).
% 11.53/1.86  fof(f332,plain,(
% 11.53/1.86    spl4_25 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 11.53/1.86  fof(f422,plain,(
% 11.53/1.86    spl4_37 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 11.53/1.86  fof(f807,plain,(
% 11.53/1.86    spl4_62 <=> r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_62])])).
% 11.53/1.86  fof(f1446,plain,(
% 11.53/1.86    spl4_115 <=> k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_115])])).
% 11.53/1.86  fof(f1574,plain,(
% 11.53/1.86    sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15 | ~spl4_18 | ~spl4_25 | ~spl4_37 | ~spl4_62 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1573,f808])).
% 11.53/1.86  fof(f808,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl4_62),
% 11.53/1.86    inference(avatar_component_clause,[],[f807])).
% 11.53/1.86  fof(f1573,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15 | ~spl4_18 | ~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(forward_demodulation,[],[f1572,f85])).
% 11.53/1.86  fof(f1572,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15 | ~spl4_18 | ~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1571,f280])).
% 11.53/1.86  fof(f1571,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15 | ~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1570,f174])).
% 11.53/1.86  fof(f1570,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1569,f148])).
% 11.53/1.86  fof(f1569,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1568,f110])).
% 11.53/1.86  fof(f1568,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_25 | ~spl4_37 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1567,f423])).
% 11.53/1.86  fof(f423,plain,(
% 11.53/1.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_37),
% 11.53/1.86    inference(avatar_component_clause,[],[f422])).
% 11.53/1.86  fof(f1567,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_25 | ~spl4_115)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1566,f333])).
% 11.53/1.86  fof(f333,plain,(
% 11.53/1.86    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_25),
% 11.53/1.86    inference(avatar_component_clause,[],[f332])).
% 11.53/1.86  fof(f1566,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_partfun1(sK0)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | sK0 = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl4_115),
% 11.53/1.86    inference(superposition,[],[f84,f1447])).
% 11.53/1.86  fof(f1447,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | ~spl4_115),
% 11.53/1.86    inference(avatar_component_clause,[],[f1446])).
% 11.53/1.86  fof(f1784,plain,(
% 11.53/1.86    spl4_51 | ~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_16 | ~spl4_113),
% 11.53/1.86    inference(avatar_split_clause,[],[f1544,f1428,f271,f173,f158,f147,f139,f109,f101,f597])).
% 11.53/1.86  fof(f1544,plain,(
% 11.53/1.86    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_16 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1543,f1514])).
% 11.53/1.86  fof(f1543,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_113)),
% 11.53/1.86    inference(forward_demodulation,[],[f1532,f85])).
% 11.53/1.86  fof(f1532,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1531,f102])).
% 11.53/1.86  fof(f1531,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_15 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1530,f174])).
% 11.53/1.86  fof(f1530,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_11 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1529,f148])).
% 11.53/1.86  fof(f1529,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_3 | ~spl4_6 | ~spl4_11 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1528,f110])).
% 11.53/1.86  fof(f1528,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_6 | ~spl4_11 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1527,f159])).
% 11.53/1.86  fof(f1527,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_6 | ~spl4_113)),
% 11.53/1.86    inference(subsumption_resolution,[],[f1517,f140])).
% 11.53/1.86  fof(f1517,plain,(
% 11.53/1.86    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_113),
% 11.53/1.86    inference(superposition,[],[f84,f1429])).
% 11.53/1.86  fof(f1640,plain,(
% 11.53/1.86    spl4_131 | ~spl4_30 | ~spl4_53),
% 11.53/1.86    inference(avatar_split_clause,[],[f1558,f608,f372,f1638])).
% 11.53/1.86  fof(f372,plain,(
% 11.53/1.86    spl4_30 <=> v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 11.53/1.86  fof(f1558,plain,(
% 11.53/1.86    v1_funct_2(sK3,k1_relat_1(sK3),sK0) | (~spl4_30 | ~spl4_53)),
% 11.53/1.86    inference(superposition,[],[f373,f1538])).
% 11.53/1.86  fof(f373,plain,(
% 11.53/1.86    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_30),
% 11.53/1.86    inference(avatar_component_clause,[],[f372])).
% 11.53/1.86  fof(f1537,plain,(
% 11.53/1.86    sK0 != k2_relset_1(sK1,sK0,sK3) | k2_relat_1(sK3) != k2_relset_1(sK1,sK0,sK3) | sK0 = k2_relat_1(sK3)),
% 11.53/1.86    introduced(theory_tautology_sat_conflict,[])).
% 11.53/1.86  fof(f1448,plain,(
% 11.53/1.86    spl4_115 | ~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_39),
% 11.53/1.86    inference(avatar_split_clause,[],[f656,f430,f422,f279,f173,f109,f1446])).
% 11.53/1.86  fof(f656,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_39)),
% 11.53/1.86    inference(forward_demodulation,[],[f655,f431])).
% 11.53/1.86  fof(f655,plain,(
% 11.53/1.86    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37)),
% 11.53/1.86    inference(subsumption_resolution,[],[f650,f280])).
% 11.53/1.86  fof(f650,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_15 | ~spl4_37)),
% 11.53/1.86    inference(resolution,[],[f251,f423])).
% 11.53/1.86  fof(f251,plain,(
% 11.53/1.86    ( ! [X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_1(X7) | k1_partfun1(sK0,sK1,X8,X9,sK2,X7) = k5_relat_1(sK2,X7)) ) | (~spl4_3 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f221,f110])).
% 11.53/1.86  fof(f221,plain,(
% 11.53/1.86    ( ! [X8,X7,X9] : (~v1_funct_1(sK2) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k1_partfun1(sK0,sK1,X8,X9,sK2,X7) = k5_relat_1(sK2,X7)) ) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f88])).
% 11.53/1.86  fof(f1430,plain,(
% 11.53/1.86    spl4_113 | ~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f651,f173,f158,f109,f101,f1428])).
% 11.53/1.86  fof(f651,plain,(
% 11.53/1.86    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | (~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f646,f102])).
% 11.53/1.86  fof(f646,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | (~spl4_3 | ~spl4_11 | ~spl4_15)),
% 11.53/1.86    inference(resolution,[],[f251,f159])).
% 11.53/1.86  fof(f1135,plain,(
% 11.53/1.86    spl4_82 | ~spl4_48),
% 11.53/1.86    inference(avatar_split_clause,[],[f569,f557,f1133])).
% 11.53/1.86  fof(f1133,plain,(
% 11.53/1.86    spl4_82 <=> k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_82])])).
% 11.53/1.86  fof(f569,plain,(
% 11.53/1.86    k2_relat_1(sK3) = k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) | ~spl4_48),
% 11.53/1.86    inference(resolution,[],[f558,f89])).
% 11.53/1.86  fof(f899,plain,(
% 11.53/1.86    spl4_76 | ~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f688,f173,f158,f109,f101,f897])).
% 11.53/1.86  fof(f688,plain,(
% 11.53/1.86    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15)),
% 11.53/1.86    inference(forward_demodulation,[],[f687,f651])).
% 11.53/1.86  fof(f687,plain,(
% 11.53/1.86    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_1 | ~spl4_3 | ~spl4_11 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f682,f102])).
% 11.53/1.86  fof(f682,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_3 | ~spl4_11 | ~spl4_15)),
% 11.53/1.86    inference(resolution,[],[f250,f159])).
% 11.53/1.86  fof(f250,plain,(
% 11.53/1.86    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | ~v1_funct_1(X4) | m1_subset_1(k1_partfun1(sK0,sK1,X5,X6,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))) ) | (~spl4_3 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f220,f110])).
% 11.53/1.86  fof(f220,plain,(
% 11.53/1.86    ( ! [X6,X4,X5] : (~v1_funct_1(sK2) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | m1_subset_1(k1_partfun1(sK0,sK1,X5,X6,sK2,X4),k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))) ) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f87])).
% 11.53/1.86  fof(f813,plain,(
% 11.53/1.86    spl4_63 | ~spl4_32 | ~spl4_37),
% 11.53/1.86    inference(avatar_split_clause,[],[f480,f422,f380,f811])).
% 11.53/1.86  fof(f811,plain,(
% 11.53/1.86    spl4_63 <=> k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 11.53/1.86  fof(f480,plain,(
% 11.53/1.86    k1_relat_1(sK2) = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | (~spl4_32 | ~spl4_37)),
% 11.53/1.86    inference(forward_demodulation,[],[f462,f381])).
% 11.53/1.86  fof(f462,plain,(
% 11.53/1.86    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~spl4_37),
% 11.53/1.86    inference(resolution,[],[f423,f89])).
% 11.53/1.86  fof(f809,plain,(
% 11.53/1.86    spl4_62 | ~spl4_59),
% 11.53/1.86    inference(avatar_split_clause,[],[f782,f768,f807])).
% 11.53/1.86  fof(f782,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | ~spl4_59),
% 11.53/1.86    inference(resolution,[],[f769,f98])).
% 11.53/1.86  fof(f770,plain,(
% 11.53/1.86    spl4_59 | ~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_39),
% 11.53/1.86    inference(avatar_split_clause,[],[f696,f430,f422,f279,f173,f109,f768])).
% 11.53/1.86  fof(f696,plain,(
% 11.53/1.86    m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37 | ~spl4_39)),
% 11.53/1.86    inference(forward_demodulation,[],[f695,f656])).
% 11.53/1.86  fof(f695,plain,(
% 11.53/1.86    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_3 | ~spl4_15 | ~spl4_18 | ~spl4_37)),
% 11.53/1.86    inference(subsumption_resolution,[],[f686,f280])).
% 11.53/1.86  fof(f686,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK2)) | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | (~spl4_3 | ~spl4_15 | ~spl4_37)),
% 11.53/1.86    inference(resolution,[],[f250,f423])).
% 11.53/1.86  fof(f737,plain,(
% 11.53/1.86    spl4_56 | ~spl4_37),
% 11.53/1.86    inference(avatar_split_clause,[],[f464,f422,f735])).
% 11.53/1.86  fof(f735,plain,(
% 11.53/1.86    spl4_56 <=> r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 11.53/1.86  fof(f464,plain,(
% 11.53/1.86    r2_relset_1(sK1,sK0,k2_funct_1(sK2),k2_funct_1(sK2)) | ~spl4_37),
% 11.53/1.86    inference(resolution,[],[f423,f98])).
% 11.53/1.86  fof(f713,plain,(
% 11.53/1.86    spl4_55 | ~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_39 | ~spl4_46),
% 11.53/1.86    inference(avatar_split_clause,[],[f709,f503,f430,f388,f380,f340,f279,f173,f166,f162,f109,f711])).
% 11.53/1.86  fof(f709,plain,(
% 11.53/1.86    sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_39 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f708,f431])).
% 11.53/1.86  fof(f708,plain,(
% 11.53/1.86    k6_relat_1(sK0) != k5_relat_1(sK2,k2_funct_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_34 | ~spl4_46)),
% 11.53/1.86    inference(forward_demodulation,[],[f707,f389])).
% 11.53/1.86  fof(f707,plain,(
% 11.53/1.86    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k1_relat_1(sK2)) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_27 | ~spl4_32 | ~spl4_46)),
% 11.53/1.86    inference(forward_demodulation,[],[f706,f381])).
% 11.53/1.86  fof(f706,plain,(
% 11.53/1.86    k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_27 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f705,f341])).
% 11.53/1.86  fof(f705,plain,(
% 11.53/1.86    sK1 != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_13 | ~spl4_15 | ~spl4_18 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f704,f167])).
% 11.53/1.86  fof(f704,plain,(
% 11.53/1.86    ~v1_relat_1(k2_funct_1(sK2)) | sK1 != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_15 | ~spl4_18 | ~spl4_46)),
% 11.53/1.86    inference(subsumption_resolution,[],[f699,f280])).
% 11.53/1.86  fof(f699,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | sK1 != k1_relat_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) != k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_12 | ~spl4_15 | ~spl4_46)),
% 11.53/1.86    inference(resolution,[],[f267,f504])).
% 11.53/1.86  fof(f625,plain,(
% 11.53/1.86    ~spl4_54 | spl4_7 | ~spl4_11 | ~spl4_37),
% 11.53/1.86    inference(avatar_split_clause,[],[f606,f422,f158,f143,f623])).
% 11.53/1.86  fof(f623,plain,(
% 11.53/1.86    spl4_54 <=> r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2))),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 11.53/1.86  fof(f143,plain,(
% 11.53/1.86    spl4_7 <=> sK3 = k2_funct_1(sK2)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 11.53/1.86  fof(f606,plain,(
% 11.53/1.86    ~r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) | (spl4_7 | ~spl4_11 | ~spl4_37)),
% 11.53/1.86    inference(subsumption_resolution,[],[f605,f144])).
% 11.53/1.86  fof(f144,plain,(
% 11.53/1.86    sK3 != k2_funct_1(sK2) | spl4_7),
% 11.53/1.86    inference(avatar_component_clause,[],[f143])).
% 11.53/1.86  fof(f605,plain,(
% 11.53/1.86    sK3 = k2_funct_1(sK2) | ~r2_relset_1(sK1,sK0,sK3,k2_funct_1(sK2)) | (~spl4_11 | ~spl4_37)),
% 11.53/1.86    inference(resolution,[],[f181,f423])).
% 11.53/1.86  fof(f181,plain,(
% 11.53/1.86    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK3 = X0 | ~r2_relset_1(sK1,sK0,sK3,X0)) ) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f83])).
% 11.53/1.86  fof(f602,plain,(
% 11.53/1.86    spl4_50 | ~spl4_51 | ~spl4_52 | ~spl4_1 | ~spl4_6 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f191,f158,f139,f101,f600,f597,f594])).
% 11.53/1.86  fof(f191,plain,(
% 11.53/1.86    ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | v1_funct_2(k2_funct_1(sK3),sK0,sK1) | (~spl4_1 | ~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f190,f102])).
% 11.53/1.86  fof(f190,plain,(
% 11.53/1.86    ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | v1_funct_2(k2_funct_1(sK3),sK0,sK1) | (~spl4_6 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f177,f140])).
% 11.53/1.86  fof(f177,plain,(
% 11.53/1.86    ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | sK0 != k2_relset_1(sK1,sK0,sK3) | v1_funct_2(k2_funct_1(sK3),sK0,sK1) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f65])).
% 11.53/1.86  fof(f65,plain,(
% 11.53/1.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 11.53/1.86    inference(cnf_transformation,[],[f25])).
% 11.53/1.86  fof(f559,plain,(
% 11.53/1.86    spl4_48 | ~spl4_1 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f209,f158,f101,f557])).
% 11.53/1.86  fof(f209,plain,(
% 11.53/1.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f113,f186])).
% 11.53/1.86  fof(f113,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) | ~spl4_1),
% 11.53/1.86    inference(resolution,[],[f102,f92])).
% 11.53/1.86  fof(f92,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f51])).
% 11.53/1.86  fof(f51,plain,(
% 11.53/1.86    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.86    inference(flattening,[],[f50])).
% 11.53/1.86  fof(f50,plain,(
% 11.53/1.86    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.86    inference(ennf_transformation,[],[f19])).
% 11.53/1.86  fof(f19,axiom,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 11.53/1.86  fof(f505,plain,(
% 11.53/1.86    spl4_46 | ~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_19 | ~spl4_27 | ~spl4_39),
% 11.53/1.86    inference(avatar_split_clause,[],[f493,f430,f340,f308,f279,f169,f166,f109,f503])).
% 11.53/1.86  fof(f169,plain,(
% 11.53/1.86    spl4_14 <=> v1_relat_1(sK2)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 11.53/1.86  fof(f308,plain,(
% 11.53/1.86    spl4_19 <=> sK1 = k2_relat_1(sK2)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 11.53/1.86  fof(f493,plain,(
% 11.53/1.86    v2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_19 | ~spl4_27 | ~spl4_39)),
% 11.53/1.86    inference(subsumption_resolution,[],[f492,f309])).
% 11.53/1.86  fof(f309,plain,(
% 11.53/1.86    sK1 = k2_relat_1(sK2) | ~spl4_19),
% 11.53/1.86    inference(avatar_component_clause,[],[f308])).
% 11.53/1.86  fof(f492,plain,(
% 11.53/1.86    sK1 != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_27 | ~spl4_39)),
% 11.53/1.86    inference(forward_demodulation,[],[f491,f341])).
% 11.53/1.86  fof(f491,plain,(
% 11.53/1.86    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_13 | ~spl4_14 | ~spl4_18 | ~spl4_39)),
% 11.53/1.86    inference(subsumption_resolution,[],[f490,f167])).
% 11.53/1.86  fof(f490,plain,(
% 11.53/1.86    ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_14 | ~spl4_18 | ~spl4_39)),
% 11.53/1.86    inference(subsumption_resolution,[],[f489,f110])).
% 11.53/1.86  fof(f489,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl4_14 | ~spl4_18 | ~spl4_39)),
% 11.53/1.86    inference(subsumption_resolution,[],[f488,f268])).
% 11.53/1.86  fof(f268,plain,(
% 11.53/1.86    v1_relat_1(sK2) | ~spl4_14),
% 11.53/1.86    inference(avatar_component_clause,[],[f169])).
% 11.53/1.86  fof(f488,plain,(
% 11.53/1.86    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | (~spl4_18 | ~spl4_39)),
% 11.53/1.86    inference(subsumption_resolution,[],[f487,f280])).
% 11.53/1.86  fof(f487,plain,(
% 11.53/1.86    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~spl4_39),
% 11.53/1.86    inference(subsumption_resolution,[],[f486,f94])).
% 11.53/1.86  fof(f486,plain,(
% 11.53/1.86    ~v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~spl4_39),
% 11.53/1.86    inference(superposition,[],[f81,f431])).
% 11.53/1.86  fof(f432,plain,(
% 11.53/1.86    spl4_39 | ~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f242,f173,f162,f147,f135,f109,f105,f430])).
% 11.53/1.86  fof(f105,plain,(
% 11.53/1.86    spl4_2 <=> v2_funct_1(sK2)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 11.53/1.86  fof(f135,plain,(
% 11.53/1.86    spl4_5 <=> k1_xboole_0 = sK1),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 11.53/1.86  fof(f242,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(forward_demodulation,[],[f241,f85])).
% 11.53/1.86  fof(f241,plain,(
% 11.53/1.86    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f240,f136])).
% 11.53/1.86  fof(f136,plain,(
% 11.53/1.86    k1_xboole_0 != sK1 | spl4_5),
% 11.53/1.86    inference(avatar_component_clause,[],[f135])).
% 11.53/1.86  fof(f240,plain,(
% 11.53/1.86    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f239,f106])).
% 11.53/1.86  fof(f106,plain,(
% 11.53/1.86    v2_funct_1(sK2) | ~spl4_2),
% 11.53/1.86    inference(avatar_component_clause,[],[f105])).
% 11.53/1.86  fof(f239,plain,(
% 11.53/1.86    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f238,f163])).
% 11.53/1.86  fof(f238,plain,(
% 11.53/1.86    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f237,f110])).
% 11.53/1.86  fof(f237,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f216,f148])).
% 11.53/1.86  fof(f216,plain,(
% 11.53/1.86    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f78])).
% 11.53/1.86  fof(f424,plain,(
% 11.53/1.86    spl4_37 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f236,f173,f162,f147,f109,f105,f422])).
% 11.53/1.86  fof(f236,plain,(
% 11.53/1.86    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f235,f163])).
% 11.53/1.86  fof(f235,plain,(
% 11.53/1.86    sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f234,f106])).
% 11.53/1.86  fof(f234,plain,(
% 11.53/1.86    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f233,f110])).
% 11.53/1.86  fof(f233,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f215,f148])).
% 11.53/1.86  fof(f215,plain,(
% 11.53/1.86    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f66])).
% 11.53/1.86  fof(f410,plain,(
% 11.53/1.86    spl4_36 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f185,f158,f408])).
% 11.53/1.86  fof(f408,plain,(
% 11.53/1.86    spl4_36 <=> k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 11.53/1.86    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 11.53/1.86  fof(f185,plain,(
% 11.53/1.86    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) | ~spl4_11),
% 11.53/1.86    inference(resolution,[],[f159,f89])).
% 11.53/1.86  fof(f390,plain,(
% 11.53/1.86    spl4_34 | ~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f259,f173,f162,f147,f135,f109,f105,f388])).
% 11.53/1.86  fof(f259,plain,(
% 11.53/1.86    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_2 | ~spl4_3 | spl4_5 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(forward_demodulation,[],[f258,f242])).
% 11.53/1.86  fof(f258,plain,(
% 11.53/1.86    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f123,f223])).
% 11.53/1.86  fof(f123,plain,(
% 11.53/1.86    ~v1_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_2 | ~spl4_3)),
% 11.53/1.86    inference(subsumption_resolution,[],[f119,f110])).
% 11.53/1.86  fof(f119,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_2),
% 11.53/1.86    inference(resolution,[],[f106,f68])).
% 11.53/1.86  fof(f68,plain,(
% 11.53/1.86    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f29])).
% 11.53/1.86  fof(f29,plain,(
% 11.53/1.86    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.86    inference(flattening,[],[f28])).
% 11.53/1.86  fof(f28,plain,(
% 11.53/1.86    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.86    inference(ennf_transformation,[],[f5])).
% 11.53/1.86  fof(f5,axiom,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 11.53/1.86  fof(f382,plain,(
% 11.53/1.86    spl4_32 | ~spl4_2 | ~spl4_3 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f257,f173,f109,f105,f380])).
% 11.53/1.86  fof(f257,plain,(
% 11.53/1.86    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f122,f223])).
% 11.53/1.86  fof(f122,plain,(
% 11.53/1.86    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3)),
% 11.53/1.86    inference(subsumption_resolution,[],[f118,f110])).
% 11.53/1.86  fof(f118,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 11.53/1.86    inference(resolution,[],[f106,f71])).
% 11.53/1.86  fof(f374,plain,(
% 11.53/1.86    spl4_30 | ~spl4_1 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f210,f158,f101,f372])).
% 11.53/1.86  fof(f210,plain,(
% 11.53/1.86    v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f112,f186])).
% 11.53/1.86  fof(f112,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) | ~spl4_1),
% 11.53/1.86    inference(resolution,[],[f102,f91])).
% 11.53/1.86  fof(f91,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f51])).
% 11.53/1.86  fof(f342,plain,(
% 11.53/1.86    spl4_27 | ~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f256,f173,f162,f109,f105,f340])).
% 11.53/1.86  fof(f256,plain,(
% 11.53/1.86    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(forward_demodulation,[],[f255,f252])).
% 11.53/1.86  fof(f255,plain,(
% 11.53/1.86    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f121,f223])).
% 11.53/1.86  fof(f121,plain,(
% 11.53/1.86    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3)),
% 11.53/1.86    inference(subsumption_resolution,[],[f117,f110])).
% 11.53/1.86  fof(f117,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 11.53/1.86    inference(resolution,[],[f106,f70])).
% 11.53/1.86  fof(f334,plain,(
% 11.53/1.86    spl4_25 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f232,f173,f162,f147,f109,f105,f332])).
% 11.53/1.86  fof(f232,plain,(
% 11.53/1.86    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f231,f163])).
% 11.53/1.86  fof(f231,plain,(
% 11.53/1.86    sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f230,f106])).
% 11.53/1.86  fof(f230,plain,(
% 11.53/1.86    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f229,f110])).
% 11.53/1.86  fof(f229,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f214,f148])).
% 11.53/1.86  fof(f214,plain,(
% 11.53/1.86    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f65])).
% 11.53/1.86  fof(f310,plain,(
% 11.53/1.86    spl4_19 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f252,f173,f162,f308])).
% 11.53/1.86  fof(f281,plain,(
% 11.53/1.86    spl4_18 | ~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f228,f173,f162,f147,f109,f105,f279])).
% 11.53/1.86  fof(f228,plain,(
% 11.53/1.86    v1_funct_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_12 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f227,f163])).
% 11.53/1.86  fof(f227,plain,(
% 11.53/1.86    sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f226,f106])).
% 11.53/1.86  fof(f226,plain,(
% 11.53/1.86    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2)) | (~spl4_3 | ~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f225,f110])).
% 11.53/1.86  fof(f225,plain,(
% 11.53/1.86    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2)) | (~spl4_8 | ~spl4_15)),
% 11.53/1.86    inference(subsumption_resolution,[],[f213,f148])).
% 11.53/1.86  fof(f213,plain,(
% 11.53/1.86    ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2)) | ~spl4_15),
% 11.53/1.86    inference(resolution,[],[f174,f64])).
% 11.53/1.86  fof(f64,plain,(
% 11.53/1.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f25])).
% 11.53/1.86  fof(f277,plain,(
% 11.53/1.86    spl4_17 | ~spl4_1 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f208,f158,f101,f275])).
% 11.53/1.86  fof(f208,plain,(
% 11.53/1.86    v1_funct_1(k2_funct_1(sK3)) | (~spl4_1 | ~spl4_11)),
% 11.53/1.86    inference(subsumption_resolution,[],[f115,f186])).
% 11.53/1.86  fof(f115,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | v1_funct_1(k2_funct_1(sK3)) | ~spl4_1),
% 11.53/1.86    inference(resolution,[],[f102,f73])).
% 11.53/1.86  fof(f73,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f33])).
% 11.53/1.86  fof(f33,plain,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.53/1.86    inference(flattening,[],[f32])).
% 11.53/1.86  fof(f32,plain,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.53/1.86    inference(ennf_transformation,[],[f1])).
% 11.53/1.86  fof(f1,axiom,(
% 11.53/1.86    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 11.53/1.86  fof(f273,plain,(
% 11.53/1.86    spl4_16),
% 11.53/1.86    inference(avatar_split_clause,[],[f99,f271])).
% 11.53/1.86  fof(f99,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 11.53/1.86    inference(forward_demodulation,[],[f56,f85])).
% 11.53/1.86  fof(f56,plain,(
% 11.53/1.86    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f23,plain,(
% 11.53/1.86    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 11.53/1.86    inference(flattening,[],[f22])).
% 11.53/1.86  fof(f22,plain,(
% 11.53/1.86    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 11.53/1.86    inference(ennf_transformation,[],[f21])).
% 11.53/1.86  fof(f21,negated_conjecture,(
% 11.53/1.86    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.53/1.86    inference(negated_conjecture,[],[f20])).
% 11.53/1.86  fof(f20,conjecture,(
% 11.53/1.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 11.53/1.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 11.53/1.86  fof(f269,plain,(
% 11.53/1.86    spl4_14 | ~spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f223,f173,f169])).
% 11.53/1.86  fof(f212,plain,(
% 11.53/1.86    spl4_10 | ~spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f186,f158,f154])).
% 11.53/1.86  fof(f175,plain,(
% 11.53/1.86    spl4_15),
% 11.53/1.86    inference(avatar_split_clause,[],[f63,f173])).
% 11.53/1.86  fof(f63,plain,(
% 11.53/1.86    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f171,plain,(
% 11.53/1.86    spl4_13 | ~spl4_14 | ~spl4_3),
% 11.53/1.86    inference(avatar_split_clause,[],[f127,f109,f169,f166])).
% 11.53/1.86  fof(f127,plain,(
% 11.53/1.86    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~spl4_3),
% 11.53/1.86    inference(resolution,[],[f110,f72])).
% 11.53/1.86  fof(f72,plain,(
% 11.53/1.86    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 11.53/1.86    inference(cnf_transformation,[],[f33])).
% 11.53/1.86  fof(f164,plain,(
% 11.53/1.86    spl4_12),
% 11.53/1.86    inference(avatar_split_clause,[],[f55,f162])).
% 11.53/1.86  fof(f55,plain,(
% 11.53/1.86    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f160,plain,(
% 11.53/1.86    spl4_11),
% 11.53/1.86    inference(avatar_split_clause,[],[f54,f158])).
% 11.53/1.86  fof(f54,plain,(
% 11.53/1.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f156,plain,(
% 11.53/1.86    spl4_9 | ~spl4_10 | ~spl4_1),
% 11.53/1.86    inference(avatar_split_clause,[],[f114,f101,f154,f151])).
% 11.53/1.86  fof(f114,plain,(
% 11.53/1.86    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~spl4_1),
% 11.53/1.86    inference(resolution,[],[f102,f72])).
% 11.53/1.86  fof(f149,plain,(
% 11.53/1.86    spl4_8),
% 11.53/1.86    inference(avatar_split_clause,[],[f62,f147])).
% 11.53/1.86  fof(f62,plain,(
% 11.53/1.86    v1_funct_2(sK2,sK0,sK1)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f145,plain,(
% 11.53/1.86    ~spl4_7),
% 11.53/1.86    inference(avatar_split_clause,[],[f60,f143])).
% 11.53/1.86  fof(f60,plain,(
% 11.53/1.86    sK3 != k2_funct_1(sK2)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f141,plain,(
% 11.53/1.86    spl4_6),
% 11.53/1.86    inference(avatar_split_clause,[],[f53,f139])).
% 11.53/1.86  fof(f53,plain,(
% 11.53/1.86    v1_funct_2(sK3,sK1,sK0)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f137,plain,(
% 11.53/1.86    ~spl4_5),
% 11.53/1.86    inference(avatar_split_clause,[],[f59,f135])).
% 11.53/1.86  fof(f59,plain,(
% 11.53/1.86    k1_xboole_0 != sK1),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f133,plain,(
% 11.53/1.86    ~spl4_4),
% 11.53/1.86    inference(avatar_split_clause,[],[f58,f131])).
% 11.53/1.86  fof(f58,plain,(
% 11.53/1.86    k1_xboole_0 != sK0),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f111,plain,(
% 11.53/1.86    spl4_3),
% 11.53/1.86    inference(avatar_split_clause,[],[f61,f109])).
% 11.53/1.86  fof(f61,plain,(
% 11.53/1.86    v1_funct_1(sK2)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f107,plain,(
% 11.53/1.86    spl4_2),
% 11.53/1.86    inference(avatar_split_clause,[],[f57,f105])).
% 11.53/1.86  fof(f57,plain,(
% 11.53/1.86    v2_funct_1(sK2)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  fof(f103,plain,(
% 11.53/1.86    spl4_1),
% 11.53/1.86    inference(avatar_split_clause,[],[f52,f101])).
% 11.53/1.86  fof(f52,plain,(
% 11.53/1.86    v1_funct_1(sK3)),
% 11.53/1.86    inference(cnf_transformation,[],[f23])).
% 11.53/1.86  % SZS output end Proof for theBenchmark
% 11.53/1.86  % (15204)------------------------------
% 11.53/1.86  % (15204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.53/1.86  % (15204)Termination reason: Refutation
% 11.53/1.86  
% 11.53/1.86  % (15204)Memory used [KB]: 12665
% 11.53/1.86  % (15204)Time elapsed: 1.413 s
% 11.53/1.86  % (15204)------------------------------
% 11.53/1.86  % (15204)------------------------------
% 11.53/1.87  % (15177)Success in time 1.501 s
%------------------------------------------------------------------------------
