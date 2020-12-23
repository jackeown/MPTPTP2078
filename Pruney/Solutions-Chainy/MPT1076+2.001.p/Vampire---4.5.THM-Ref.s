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
% DateTime   : Thu Dec  3 13:08:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 510 expanded)
%              Number of leaves         :   61 ( 257 expanded)
%              Depth                    :   10
%              Number of atoms          :  936 (2520 expanded)
%              Number of equality atoms :   92 ( 272 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f444,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f143,f152,f158,f162,f187,f205,f207,f223,f236,f239,f252,f273,f283,f285,f288,f294,f301,f309,f317,f322,f341,f344,f351,f425,f433,f438,f442,f443])).

fof(f443,plain,
    ( k1_xboole_0 != sK1
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f442,plain,
    ( ~ spl6_6
    | spl6_60 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl6_6
    | spl6_60 ),
    inference(subsumption_resolution,[],[f110,f439])).

fof(f439,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | spl6_60 ),
    inference(resolution,[],[f437,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f437,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl6_60 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl6_60
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f110,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl6_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f438,plain,
    ( ~ spl6_16
    | ~ spl6_60
    | spl6_59 ),
    inference(avatar_split_clause,[],[f434,f431,f436,f165])).

fof(f165,plain,
    ( spl6_16
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f431,plain,
    ( spl6_59
  <=> r1_tarski(k2_relat_1(sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).

fof(f434,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | spl6_59 ),
    inference(resolution,[],[f432,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f432,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | spl6_59 ),
    inference(avatar_component_clause,[],[f431])).

fof(f433,plain,
    ( ~ spl6_6
    | ~ spl6_59
    | spl6_58 ),
    inference(avatar_split_clause,[],[f429,f423,f431,f109])).

fof(f423,plain,
    ( spl6_58
  <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f429,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl6_58 ),
    inference(superposition,[],[f424,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f424,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | spl6_58 ),
    inference(avatar_component_clause,[],[f423])).

fof(f425,plain,
    ( spl6_10
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | spl6_57
    | ~ spl6_58
    | ~ spl6_12
    | spl6_46 ),
    inference(avatar_split_clause,[],[f418,f349,f140,f423,f420,f97,f101,f105,f109,f113,f117,f125])).

fof(f125,plain,
    ( spl6_10
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f117,plain,
    ( spl6_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f113,plain,
    ( spl6_7
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f105,plain,
    ( spl6_5
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f101,plain,
    ( spl6_4
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f97,plain,
    ( spl6_3
  <=> m1_subset_1(sK5,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f420,plain,
    ( spl6_57
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).

fof(f140,plain,
    ( spl6_12
  <=> sK0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f349,plain,
    ( spl6_46
  <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f418,plain,
    ( ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | ~ spl6_12
    | spl6_46 ),
    inference(forward_demodulation,[],[f417,f141])).

fof(f141,plain,
    ( sK0 = k1_relat_1(sK4)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f417,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl6_46 ),
    inference(trivial_inequality_removal,[],[f416])).

fof(f416,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | k1_xboole_0 = sK1
    | ~ r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4))
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK0)
    | spl6_46 ),
    inference(superposition,[],[f350,f370])).

fof(f370,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_funct_1(k8_funct_2(X3,X0,X1,X4,X2),X5) = k1_funct_1(X2,k1_funct_1(X4,X5))
      | k1_xboole_0 = X3
      | ~ r1_tarski(k2_relset_1(X3,X0,X4),k1_relat_1(X2))
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f369])).

fof(f369,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X3,X0,X4),k1_relat_1(X2))
      | k1_xboole_0 = X3
      | k1_funct_1(k8_funct_2(X3,X0,X1,X4,X2),X5) = k1_funct_1(X2,k1_funct_1(X4,X5))
      | ~ m1_subset_1(X5,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0)))
      | ~ v1_funct_2(X4,X3,X0)
      | ~ v1_funct_1(X4)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f74,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
      | k1_xboole_0 = X1
      | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
      | ~ m1_subset_1(X5,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X3,X1,X2)
      | ~ v1_funct_1(X3)
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                  | k1_xboole_0 = X1
                  | ~ r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                  | ~ m1_subset_1(X5,X1) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
              | ~ v1_funct_1(X4) )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X3,X1,X2)
          | ~ v1_funct_1(X3) )
      | v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X3,X1,X2)
            & v1_funct_1(X3) )
         => ! [X4] :
              ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                & v1_funct_1(X4) )
             => ! [X5] :
                  ( m1_subset_1(X5,X1)
                 => ( r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))
                   => ( k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5))
                      | k1_xboole_0 = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).

fof(f350,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_46 ),
    inference(avatar_component_clause,[],[f349])).

fof(f351,plain,
    ( ~ spl6_46
    | spl6_21
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_41 ),
    inference(avatar_split_clause,[],[f347,f314,f298,f292,f185,f349])).

fof(f185,plain,
    ( spl6_21
  <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f292,plain,
    ( spl6_37
  <=> k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f298,plain,
    ( spl6_38
  <=> k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f314,plain,
    ( spl6_41
  <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).

fof(f347,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5))
    | spl6_21
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_41 ),
    inference(forward_demodulation,[],[f346,f315])).

fof(f315,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_41 ),
    inference(avatar_component_clause,[],[f314])).

fof(f346,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | spl6_21
    | ~ spl6_37
    | ~ spl6_38 ),
    inference(forward_demodulation,[],[f345,f299])).

fof(f299,plain,
    ( k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f298])).

fof(f345,plain,
    ( k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k7_partfun1(sK0,sK3,sK5))
    | spl6_21
    | ~ spl6_37 ),
    inference(forward_demodulation,[],[f186,f293])).

fof(f293,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ spl6_37 ),
    inference(avatar_component_clause,[],[f292])).

fof(f186,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | spl6_21 ),
    inference(avatar_component_clause,[],[f185])).

fof(f344,plain,
    ( spl6_20
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_6
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f342,f339,f109,f117,f113,f181])).

fof(f181,plain,
    ( spl6_20
  <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f339,plain,
    ( spl6_45
  <=> ! [X3,X2] :
        ( m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f342,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_6
    | ~ spl6_45 ),
    inference(resolution,[],[f340,f110])).

fof(f340,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,X2,sK0)
        | m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f339])).

fof(f341,plain,
    ( ~ spl6_5
    | spl6_45
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f333,f101,f339,f105])).

fof(f333,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))
        | ~ v1_funct_1(sK4)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0)))
        | ~ v1_funct_2(X3,X2,sK0)
        | ~ v1_funct_1(X3) )
    | ~ spl6_4 ),
    inference(resolution,[],[f86,f102])).

fof(f102,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f101])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) )
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
        & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).

fof(f322,plain,
    ( ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_19 ),
    inference(avatar_split_clause,[],[f321,f178,f101,f105,f109,f113,f117])).

fof(f178,plain,
    ( spl6_19
  <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f321,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl6_19 ),
    inference(resolution,[],[f85,f179])).

fof(f179,plain,
    ( ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | spl6_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f317,plain,
    ( spl6_10
    | ~ spl6_5
    | ~ spl6_35
    | ~ spl6_4
    | ~ spl6_30
    | spl6_41
    | ~ spl6_40 ),
    inference(avatar_split_clause,[],[f311,f307,f314,f250,f101,f278,f105,f125])).

fof(f278,plain,
    ( spl6_35
  <=> v1_funct_2(sK4,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f250,plain,
    ( spl6_30
  <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f307,plain,
    ( spl6_40
  <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).

fof(f311,plain,
    ( k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK4,sK0,sK2)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK0)
    | ~ spl6_40 ),
    inference(superposition,[],[f83,f308])).

fof(f308,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_40 ),
    inference(avatar_component_clause,[],[f307])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3)
      | ~ m1_subset_1(X3,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,X0)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2)
        & ~ v1_xboole_0(X0) )
     => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).

fof(f309,plain,
    ( spl6_40
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(avatar_split_clause,[],[f305,f281,f250,f307])).

fof(f281,plain,
    ( spl6_36
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f305,plain,
    ( k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))
    | ~ spl6_30
    | ~ spl6_36 ),
    inference(resolution,[],[f282,f251])).

fof(f251,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f250])).

fof(f282,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) )
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f281])).

fof(f301,plain,
    ( spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_3
    | spl6_38
    | ~ spl6_37 ),
    inference(avatar_split_clause,[],[f296,f292,f298,f97,f109,f113,f117,f121])).

fof(f121,plain,
    ( spl6_9
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f296,plain,
    ( k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | v1_xboole_0(sK1)
    | ~ spl6_37 ),
    inference(superposition,[],[f83,f293])).

fof(f294,plain,
    ( spl6_37
    | ~ spl6_3
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f290,f271,f97,f292])).

fof(f271,plain,
    ( spl6_33
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f290,plain,
    ( k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)
    | ~ spl6_3
    | ~ spl6_33 ),
    inference(resolution,[],[f272,f98])).

fof(f98,plain,
    ( m1_subset_1(sK5,sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f97])).

fof(f272,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f271])).

fof(f288,plain,
    ( spl6_10
    | ~ spl6_2
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f287,f275,f101,f93,f125])).

fof(f93,plain,
    ( spl6_2
  <=> v1_partfun1(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f275,plain,
    ( spl6_34
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f287,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | v1_xboole_0(sK0)
    | ~ spl6_4
    | ~ spl6_34 ),
    inference(resolution,[],[f286,f102])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2)))
        | ~ v1_partfun1(X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl6_34 ),
    inference(resolution,[],[f276,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_partfun1(X2,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ~ v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).

fof(f276,plain,
    ( v1_xboole_0(sK2)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f275])).

fof(f285,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | ~ spl6_2
    | spl6_35 ),
    inference(avatar_split_clause,[],[f284,f278,f93,f105,f101])).

fof(f284,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl6_35 ),
    inference(resolution,[],[f279,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

fof(f279,plain,
    ( ~ v1_funct_2(sK4,sK0,sK2)
    | spl6_35 ),
    inference(avatar_component_clause,[],[f278])).

fof(f283,plain,
    ( spl6_10
    | spl6_34
    | ~ spl6_5
    | ~ spl6_35
    | spl6_36
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f269,f101,f281,f278,f105,f275,f125])).

fof(f269,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,sK0)
        | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1)
        | ~ v1_funct_2(sK4,sK0,sK2)
        | ~ v1_funct_1(sK4)
        | v1_xboole_0(sK2)
        | v1_xboole_0(sK0) )
    | ~ spl6_4 ),
    inference(resolution,[],[f65,f102])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,X0)
      | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)
                  | ~ m1_subset_1(X3,X0) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X2,X0,X1)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X2,X0,X1)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,X0)
                 => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).

fof(f273,plain,
    ( spl6_9
    | spl6_10
    | ~ spl6_8
    | ~ spl6_7
    | spl6_33
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f268,f109,f271,f113,f117,f125,f121])).

fof(f268,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,sK1)
        | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)
        | ~ v1_funct_2(sK3,sK1,sK0)
        | ~ v1_funct_1(sK3)
        | v1_xboole_0(sK0)
        | v1_xboole_0(sK1) )
    | ~ spl6_6 ),
    inference(resolution,[],[f65,f110])).

fof(f252,plain,
    ( spl6_30
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f248,f221,f109,f97,f250])).

fof(f221,plain,
    ( spl6_27
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ m1_subset_1(X0,sK1)
        | ~ v5_relat_1(sK3,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f248,plain,
    ( m1_subset_1(k1_funct_1(sK3,sK5),sK0)
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_27 ),
    inference(resolution,[],[f225,f110])).

fof(f225,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | m1_subset_1(k1_funct_1(sK3,sK5),X0) )
    | ~ spl6_3
    | ~ spl6_27 ),
    inference(resolution,[],[f224,f79])).

fof(f224,plain,
    ( ! [X0] :
        ( ~ v5_relat_1(sK3,X0)
        | m1_subset_1(k1_funct_1(sK3,sK5),X0) )
    | ~ spl6_3
    | ~ spl6_27 ),
    inference(resolution,[],[f222,f98])).

fof(f222,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,sK1)
        | m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ v5_relat_1(sK3,X1) )
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f221])).

fof(f239,plain,
    ( ~ spl6_6
    | spl6_16 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl6_6
    | spl6_16 ),
    inference(subsumption_resolution,[],[f110,f237])).

fof(f237,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_16 ),
    inference(resolution,[],[f166,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f166,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_16 ),
    inference(avatar_component_clause,[],[f165])).

fof(f236,plain,
    ( ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_18 ),
    inference(avatar_split_clause,[],[f231,f175,f101,f105,f109,f113,f117])).

fof(f175,plain,
    ( spl6_18
  <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl6_18 ),
    inference(resolution,[],[f84,f176])).

fof(f176,plain,
    ( ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | spl6_18 ),
    inference(avatar_component_clause,[],[f175])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f223,plain,
    ( spl6_9
    | spl6_27
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f219,f203,f221,f121])).

fof(f203,plain,
    ( spl6_25
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,sK1)
        | m1_subset_1(k1_funct_1(sK3,X4),X5)
        | ~ v5_relat_1(sK3,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f219,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_funct_1(sK3,X0),X1)
        | ~ v5_relat_1(sK3,X1)
        | v1_xboole_0(sK1)
        | ~ m1_subset_1(X0,sK1) )
    | ~ spl6_25 ),
    inference(resolution,[],[f204,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f204,plain,
    ( ! [X4,X5] :
        ( ~ r2_hidden(X4,sK1)
        | m1_subset_1(k1_funct_1(sK3,X4),X5)
        | ~ v5_relat_1(sK3,X5) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f203])).

fof(f207,plain,
    ( ~ spl6_6
    | ~ spl6_24 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl6_6
    | ~ spl6_24 ),
    inference(subsumption_resolution,[],[f110,f201])).

fof(f201,plain,
    ( ! [X6,X7] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl6_24
  <=> ! [X7,X6] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f205,plain,
    ( spl6_24
    | spl6_25
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f198,f147,f117,f203,f200])).

fof(f147,plain,
    ( spl6_13
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f198,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X4,sK1)
        | ~ v5_relat_1(sK3,X5)
        | m1_subset_1(k1_funct_1(sK3,X4),X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl6_8
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f189,f148])).

fof(f148,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f189,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ r2_hidden(X4,k1_relat_1(sK3))
        | ~ v5_relat_1(sK3,X5)
        | m1_subset_1(k1_funct_1(sK3,X4),X5)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) )
    | ~ spl6_8 ),
    inference(resolution,[],[f134,f118])).

fof(f118,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f134,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v5_relat_1(X1,X2)
      | m1_subset_1(k1_funct_1(X1,X0),X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(resolution,[],[f82,f75])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | m1_subset_1(k1_funct_1(X2,X1),X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_funct_1(X2,X1),X0)
      | ~ r2_hidden(X1,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v5_relat_1(X2,X0)
        & v1_relat_1(X2) )
     => ( r2_hidden(X1,k1_relat_1(X2))
       => m1_subset_1(k1_funct_1(X2,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).

fof(f187,plain,
    ( spl6_9
    | ~ spl6_18
    | ~ spl6_19
    | ~ spl6_20
    | ~ spl6_3
    | ~ spl6_21
    | spl6_1 ),
    inference(avatar_split_clause,[],[f172,f89,f185,f97,f181,f178,f175,f121])).

fof(f89,plain,
    ( spl6_1
  <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f172,plain,
    ( k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)
    | ~ m1_subset_1(sK5,sK1)
    | ~ m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)
    | ~ v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))
    | v1_xboole_0(sK1)
    | spl6_1 ),
    inference(superposition,[],[f90,f83])).

fof(f90,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f162,plain,
    ( ~ spl6_7
    | spl6_10
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f159,f156,f109,f125,f113])).

fof(f156,plain,
    ( spl6_15
  <=> ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f159,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl6_6
    | ~ spl6_15 ),
    inference(resolution,[],[f157,f110])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK3,sK1,X0) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f158,plain,
    ( ~ spl6_8
    | spl6_15
    | spl6_14 ),
    inference(avatar_split_clause,[],[f153,f150,f156,f117])).

fof(f150,plain,
    ( spl6_14
  <=> v1_partfun1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f153,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK3,sK1,X0)
        | ~ v1_funct_1(sK3)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | v1_xboole_0(X0) )
    | spl6_14 ),
    inference(resolution,[],[f151,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f151,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f150])).

fof(f152,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f145,f109,f150,f147])).

fof(f145,plain,
    ( ~ v1_partfun1(sK3,sK1)
    | sK1 = k1_relat_1(sK3)
    | ~ spl6_6 ),
    inference(resolution,[],[f137,f110])).

fof(f137,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_partfun1(sK3,X2)
        | k1_relat_1(sK3) = X2 )
    | ~ spl6_6 ),
    inference(resolution,[],[f135,f110])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4))) ) ),
    inference(resolution,[],[f132,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_relat_1(X0,X1)
      | ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f72,f75])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

% (14414)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f31,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f143,plain,
    ( spl6_12
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f138,f101,f93,f140])).

fof(f138,plain,
    ( ~ v1_partfun1(sK4,sK0)
    | sK0 = k1_relat_1(sK4)
    | ~ spl6_4 ),
    inference(resolution,[],[f136,f102])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_partfun1(sK4,X0)
        | k1_relat_1(sK4) = X0 )
    | ~ spl6_4 ),
    inference(resolution,[],[f135,f102])).

fof(f131,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f64,f129])).

fof(f129,plain,
    ( spl6_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f127,plain,(
    ~ spl6_10 ),
    inference(avatar_split_clause,[],[f54,f125])).

fof(f54,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
    & v1_partfun1(sK4,sK0)
    & m1_subset_1(sK5,sK1)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f50,f49,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2,X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                        & v1_partfun1(X4,X0)
                        & m1_subset_1(X5,X1) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X3,X2] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                      & v1_partfun1(X4,sK0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
              & v1_funct_2(X3,X1,sK0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ? [X3,X2] :
            ( ? [X4] :
                ( ? [X5] :
                    ( k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5))
                    & v1_partfun1(X4,sK0)
                    & m1_subset_1(X5,X1) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
                & v1_funct_1(X4) )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
            & v1_funct_2(X3,X1,sK0)
            & v1_funct_1(X3) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X3,X2] :
          ( ? [X4] :
              ( ? [X5] :
                  ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                  & v1_partfun1(X4,sK0)
                  & m1_subset_1(X5,sK1) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
              & v1_funct_1(X4) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3,X2] :
        ( ? [X4] :
            ( ? [X5] :
                ( k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5))
                & v1_partfun1(X4,sK0)
                & m1_subset_1(X5,sK1) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
              & v1_partfun1(X4,sK0)
              & m1_subset_1(X5,sK1) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5))
            & v1_partfun1(X4,sK0)
            & m1_subset_1(X5,sK1) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
          & v1_partfun1(sK4,sK0)
          & m1_subset_1(X5,sK1) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X5] :
        ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5))
        & v1_partfun1(sK4,sK0)
        & m1_subset_1(X5,sK1) )
   => ( k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))
      & v1_partfun1(sK4,sK0)
      & m1_subset_1(sK5,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2,X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))
                      & v1_partfun1(X4,X0)
                      & m1_subset_1(X5,X1) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2,X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                  & v1_funct_2(X3,X1,X0)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                      & v1_funct_1(X4) )
                   => ! [X5] :
                        ( m1_subset_1(X5,X1)
                       => ( v1_partfun1(X4,X0)
                         => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2,X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
                & v1_funct_2(X3,X1,X0)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( m1_subset_1(X5,X1)
                     => ( v1_partfun1(X4,X0)
                       => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).

fof(f123,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f55,f121])).

fof(f55,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f119,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f56,f117])).

fof(f56,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f115,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f57,f113])).

fof(f57,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f111,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f58,f109])).

fof(f58,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f59,f105])).

fof(f59,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f103,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f60,f101])).

fof(f60,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f51])).

fof(f99,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f61,f97])).

fof(f61,plain,(
    m1_subset_1(sK5,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f95,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f62,f93])).

fof(f62,plain,(
    v1_partfun1(sK4,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f63,f89])).

fof(f63,plain,(
    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:45:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (14413)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.49  % (14405)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (14408)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.49  % (14416)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (14405)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % (14412)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f91,f95,f99,f103,f107,f111,f115,f119,f123,f127,f131,f143,f152,f158,f162,f187,f205,f207,f223,f236,f239,f252,f273,f283,f285,f288,f294,f301,f309,f317,f322,f341,f344,f351,f425,f433,f438,f442,f443])).
% 0.22/0.50  fof(f443,plain,(
% 0.22/0.50    k1_xboole_0 != sK1 | v1_xboole_0(sK1) | ~v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.50  fof(f442,plain,(
% 0.22/0.50    ~spl6_6 | spl6_60),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f441])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    $false | (~spl6_6 | spl6_60)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f439])).
% 0.22/0.50  fof(f439,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))) ) | spl6_60),
% 0.22/0.50    inference(resolution,[],[f437,f79])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.50  fof(f437,plain,(
% 0.22/0.50    ~v5_relat_1(sK3,sK0) | spl6_60),
% 0.22/0.50    inference(avatar_component_clause,[],[f436])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    spl6_60 <=> v5_relat_1(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl6_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f109])).
% 0.22/0.50  fof(f109,plain,(
% 0.22/0.50    spl6_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.22/0.50  fof(f438,plain,(
% 0.22/0.50    ~spl6_16 | ~spl6_60 | spl6_59),
% 0.22/0.50    inference(avatar_split_clause,[],[f434,f431,f436,f165])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl6_16 <=> v1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    spl6_59 <=> r1_tarski(k2_relat_1(sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_59])])).
% 0.22/0.50  fof(f434,plain,(
% 0.22/0.50    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | spl6_59),
% 0.22/0.50    inference(resolution,[],[f432,f68])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.50  fof(f432,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3),sK0) | spl6_59),
% 0.22/0.50    inference(avatar_component_clause,[],[f431])).
% 0.22/0.50  fof(f433,plain,(
% 0.22/0.50    ~spl6_6 | ~spl6_59 | spl6_58),
% 0.22/0.50    inference(avatar_split_clause,[],[f429,f423,f431,f109])).
% 0.22/0.50  fof(f423,plain,(
% 0.22/0.50    spl6_58 <=> r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).
% 0.22/0.50  fof(f429,plain,(
% 0.22/0.50    ~r1_tarski(k2_relat_1(sK3),sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl6_58),
% 0.22/0.50    inference(superposition,[],[f424,f77])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.50  fof(f424,plain,(
% 0.22/0.50    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | spl6_58),
% 0.22/0.50    inference(avatar_component_clause,[],[f423])).
% 0.22/0.50  fof(f425,plain,(
% 0.22/0.50    spl6_10 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | ~spl6_3 | spl6_57 | ~spl6_58 | ~spl6_12 | spl6_46),
% 0.22/0.50    inference(avatar_split_clause,[],[f418,f349,f140,f423,f420,f97,f101,f105,f109,f113,f117,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    spl6_10 <=> v1_xboole_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl6_8 <=> v1_funct_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    spl6_7 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl6_5 <=> v1_funct_1(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    spl6_4 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.22/0.50  fof(f97,plain,(
% 0.22/0.50    spl6_3 <=> m1_subset_1(sK5,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    spl6_57 <=> k1_xboole_0 = sK1),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_57])])).
% 0.22/0.50  fof(f140,plain,(
% 0.22/0.50    spl6_12 <=> sK0 = k1_relat_1(sK4)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.22/0.50  fof(f349,plain,(
% 0.22/0.50    spl6_46 <=> k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k1_funct_1(sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    ~r1_tarski(k2_relset_1(sK1,sK0,sK3),sK0) | k1_xboole_0 = sK1 | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | (~spl6_12 | spl6_46)),
% 0.22/0.50    inference(forward_demodulation,[],[f417,f141])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    sK0 = k1_relat_1(sK4) | ~spl6_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f140])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl6_46),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f416])).
% 0.22/0.50  fof(f416,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | k1_xboole_0 = sK1 | ~r1_tarski(k2_relset_1(sK1,sK0,sK3),k1_relat_1(sK4)) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | spl6_46),
% 0.22/0.50    inference(superposition,[],[f350,f370])).
% 0.22/0.50  fof(f370,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (k1_funct_1(k8_funct_2(X3,X0,X1,X4,X2),X5) = k1_funct_1(X2,k1_funct_1(X4,X5)) | k1_xboole_0 = X3 | ~r1_tarski(k2_relset_1(X3,X0,X4),k1_relat_1(X2)) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(duplicate_literal_removal,[],[f369])).
% 0.22/0.50  fof(f369,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X3,X0,X4),k1_relat_1(X2)) | k1_xboole_0 = X3 | k1_funct_1(k8_funct_2(X3,X0,X1,X4,X2),X5) = k1_funct_1(X2,k1_funct_1(X4,X5)) | ~m1_subset_1(X5,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) | ~v1_funct_2(X4,X3,X0) | ~v1_funct_1(X4) | v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(superposition,[],[f74,f76])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f35])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.50  fof(f74,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X5,X3,X1] : (~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | k1_xboole_0 = X1 | k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | ~m1_subset_1(X5,X1) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3) | v1_xboole_0(X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1 | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) | ~m1_subset_1(X5,X1)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3)) | v1_xboole_0(X2))),
% 0.22/0.50    inference(flattening,[],[f32])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (! [X3] : (! [X4] : (! [X5] : (((k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1) | ~r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4))) | ~m1_subset_1(X5,X1)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X3,X1,X2) | ~v1_funct_1(X3))) | v1_xboole_0(X2))),
% 0.22/0.50    inference(ennf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (r1_tarski(k2_relset_1(X1,X2,X3),k1_relset_1(X2,X0,X4)) => (k1_funct_1(k8_funct_2(X1,X2,X0,X3,X4),X5) = k1_funct_1(X4,k1_funct_1(X3,X5)) | k1_xboole_0 = X1))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t185_funct_2)).
% 0.22/0.50  fof(f350,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | spl6_46),
% 0.22/0.50    inference(avatar_component_clause,[],[f349])).
% 0.22/0.50  fof(f351,plain,(
% 0.22/0.50    ~spl6_46 | spl6_21 | ~spl6_37 | ~spl6_38 | ~spl6_41),
% 0.22/0.50    inference(avatar_split_clause,[],[f347,f314,f298,f292,f185,f349])).
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    spl6_21 <=> k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) = k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 0.22/0.50  fof(f292,plain,(
% 0.22/0.50    spl6_37 <=> k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    spl6_38 <=> k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.22/0.50  fof(f314,plain,(
% 0.22/0.50    spl6_41 <=> k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_41])])).
% 0.22/0.50  fof(f347,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k1_funct_1(sK4,k1_funct_1(sK3,sK5)) | (spl6_21 | ~spl6_37 | ~spl6_38 | ~spl6_41)),
% 0.22/0.50    inference(forward_demodulation,[],[f346,f315])).
% 0.22/0.50  fof(f315,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_41),
% 0.22/0.50    inference(avatar_component_clause,[],[f314])).
% 0.22/0.50  fof(f346,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (spl6_21 | ~spl6_37 | ~spl6_38)),
% 0.22/0.50    inference(forward_demodulation,[],[f345,f299])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | ~spl6_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f298])).
% 0.22/0.50  fof(f345,plain,(
% 0.22/0.50    k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k7_partfun1(sK0,sK3,sK5)) | (spl6_21 | ~spl6_37)),
% 0.22/0.50    inference(forward_demodulation,[],[f186,f293])).
% 0.22/0.50  fof(f293,plain,(
% 0.22/0.50    k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | ~spl6_37),
% 0.22/0.50    inference(avatar_component_clause,[],[f292])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | spl6_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f185])).
% 0.22/0.50  fof(f344,plain,(
% 0.22/0.50    spl6_20 | ~spl6_7 | ~spl6_8 | ~spl6_6 | ~spl6_45),
% 0.22/0.50    inference(avatar_split_clause,[],[f342,f339,f109,f117,f113,f181])).
% 0.22/0.50  fof(f181,plain,(
% 0.22/0.50    spl6_20 <=> m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.22/0.50  fof(f339,plain,(
% 0.22/0.50    spl6_45 <=> ! [X3,X2] : (m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.22/0.50  fof(f342,plain,(
% 0.22/0.50    ~v1_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | (~spl6_6 | ~spl6_45)),
% 0.22/0.50    inference(resolution,[],[f340,f110])).
% 0.22/0.50  fof(f340,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X2,sK0) | m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2)))) ) | ~spl6_45),
% 0.22/0.50    inference(avatar_component_clause,[],[f339])).
% 0.22/0.50  fof(f341,plain,(
% 0.22/0.50    ~spl6_5 | spl6_45 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f333,f101,f339,f105])).
% 0.22/0.50  fof(f333,plain,(
% 0.22/0.50    ( ! [X2,X3] : (m1_subset_1(k8_funct_2(X2,sK0,sK2,X3,sK4),k1_zfmisc_1(k2_zfmisc_1(X2,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK0))) | ~v1_funct_2(X3,X2,sK0) | ~v1_funct_1(X3)) ) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f86,f102])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl6_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f101])).
% 0.22/0.50  fof(f86,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.50    inference(flattening,[],[f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.50    inference(ennf_transformation,[],[f13])).
% 0.22/0.50  fof(f13,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3,X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (m1_subset_1(k8_funct_2(X0,X1,X2,X3,X4),k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) & v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_funct_2)).
% 0.22/0.50  fof(f322,plain,(
% 0.22/0.50    ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f321,f178,f101,f105,f109,f113,f117])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl6_19 <=> v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).
% 0.22/0.50  fof(f321,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl6_19),
% 0.22/0.50    inference(resolution,[],[f85,f179])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | spl6_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f178])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_2(k8_funct_2(X0,X1,X2,X3,X4),X0,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f317,plain,(
% 0.22/0.50    spl6_10 | ~spl6_5 | ~spl6_35 | ~spl6_4 | ~spl6_30 | spl6_41 | ~spl6_40),
% 0.22/0.50    inference(avatar_split_clause,[],[f311,f307,f314,f250,f101,f278,f105,f125])).
% 0.22/0.50  fof(f278,plain,(
% 0.22/0.50    spl6_35 <=> v1_funct_2(sK4,sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.22/0.50  fof(f250,plain,(
% 0.22/0.50    spl6_30 <=> m1_subset_1(k1_funct_1(sK3,sK5),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.22/0.50  fof(f307,plain,(
% 0.22/0.50    spl6_40 <=> k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_40])])).
% 0.22/0.50  fof(f311,plain,(
% 0.22/0.50    k1_funct_1(sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK4,sK0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK0) | ~spl6_40),
% 0.22/0.50    inference(superposition,[],[f83,f308])).
% 0.22/0.50  fof(f308,plain,(
% 0.22/0.50    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | ~spl6_40),
% 0.22/0.50    inference(avatar_component_clause,[],[f307])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | ~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ! [X0,X1,X2,X3] : (k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3) | (~m1_subset_1(X3,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,axiom,(
% 0.22/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,X0) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & ~v1_xboole_0(X0)) => k3_funct_2(X0,X1,X2,X3) = k1_funct_1(X2,X3))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_funct_2)).
% 0.22/0.50  fof(f309,plain,(
% 0.22/0.50    spl6_40 | ~spl6_30 | ~spl6_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f305,f281,f250,f307])).
% 0.22/0.50  fof(f281,plain,(
% 0.22/0.50    spl6_36 <=> ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    k3_funct_2(sK0,sK2,sK4,k1_funct_1(sK3,sK5)) = k7_partfun1(sK2,sK4,k1_funct_1(sK3,sK5)) | (~spl6_30 | ~spl6_36)),
% 0.22/0.50    inference(resolution,[],[f282,f251])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | ~spl6_30),
% 0.22/0.50    inference(avatar_component_clause,[],[f250])).
% 0.22/0.50  fof(f282,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1)) ) | ~spl6_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f281])).
% 0.22/0.50  fof(f301,plain,(
% 0.22/0.50    spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_3 | spl6_38 | ~spl6_37),
% 0.22/0.50    inference(avatar_split_clause,[],[f296,f292,f298,f97,f109,f113,f117,f121])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    spl6_9 <=> v1_xboole_0(sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    k1_funct_1(sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK1) | ~spl6_37),
% 0.22/0.50    inference(superposition,[],[f83,f293])).
% 0.22/0.50  fof(f294,plain,(
% 0.22/0.50    spl6_37 | ~spl6_3 | ~spl6_33),
% 0.22/0.50    inference(avatar_split_clause,[],[f290,f271,f97,f292])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    spl6_33 <=> ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.22/0.50  fof(f290,plain,(
% 0.22/0.50    k3_funct_2(sK1,sK0,sK3,sK5) = k7_partfun1(sK0,sK3,sK5) | (~spl6_3 | ~spl6_33)),
% 0.22/0.50    inference(resolution,[],[f272,f98])).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    m1_subset_1(sK5,sK1) | ~spl6_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f97])).
% 0.22/0.50  fof(f272,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0)) ) | ~spl6_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f271])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    spl6_10 | ~spl6_2 | ~spl6_4 | ~spl6_34),
% 0.22/0.50    inference(avatar_split_clause,[],[f287,f275,f101,f93,f125])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl6_2 <=> v1_partfun1(sK4,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.22/0.50  fof(f275,plain,(
% 0.22/0.50    spl6_34 <=> v1_xboole_0(sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~v1_partfun1(sK4,sK0) | v1_xboole_0(sK0) | (~spl6_4 | ~spl6_34)),
% 0.22/0.50    inference(resolution,[],[f286,f102])).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK2))) | ~v1_partfun1(X0,X1) | v1_xboole_0(X1)) ) | ~spl6_34),
% 0.22/0.50    inference(resolution,[],[f276,f71])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(X2,X0) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f28])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ~v1_partfun1(X2,X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_partfun1)).
% 0.22/0.50  fof(f276,plain,(
% 0.22/0.50    v1_xboole_0(sK2) | ~spl6_34),
% 0.22/0.50    inference(avatar_component_clause,[],[f275])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    ~spl6_4 | ~spl6_5 | ~spl6_2 | spl6_35),
% 0.22/0.50    inference(avatar_split_clause,[],[f284,f278,f93,f105,f101])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    ~v1_partfun1(sK4,sK0) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | spl6_35),
% 0.22/0.50    inference(resolution,[],[f279,f81])).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f39])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(flattening,[],[f38])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).
% 0.22/0.50  fof(f279,plain,(
% 0.22/0.50    ~v1_funct_2(sK4,sK0,sK2) | spl6_35),
% 0.22/0.50    inference(avatar_component_clause,[],[f278])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    spl6_10 | spl6_34 | ~spl6_5 | ~spl6_35 | spl6_36 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f269,f101,f281,f278,f105,f275,f125])).
% 0.22/0.50  fof(f269,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,sK0) | k3_funct_2(sK0,sK2,sK4,X1) = k7_partfun1(sK2,sK4,X1) | ~v1_funct_2(sK4,sK0,sK2) | ~v1_funct_1(sK4) | v1_xboole_0(sK2) | v1_xboole_0(sK0)) ) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f65,f102])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,X0) | k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3) | ~m1_subset_1(X3,X0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f15])).
% 0.22/0.50  fof(f15,axiom,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,X0) => k3_funct_2(X0,X1,X2,X3) = k7_partfun1(X1,X2,X3)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_2)).
% 0.22/0.50  fof(f273,plain,(
% 0.22/0.50    spl6_9 | spl6_10 | ~spl6_8 | ~spl6_7 | spl6_33 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f268,f109,f271,f113,f117,f125,f121])).
% 0.22/0.50  fof(f268,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,sK1) | k3_funct_2(sK1,sK0,sK3,X0) = k7_partfun1(sK0,sK3,X0) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | v1_xboole_0(sK0) | v1_xboole_0(sK1)) ) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f65,f110])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    spl6_30 | ~spl6_3 | ~spl6_6 | ~spl6_27),
% 0.22/0.50    inference(avatar_split_clause,[],[f248,f221,f109,f97,f250])).
% 0.22/0.50  fof(f221,plain,(
% 0.22/0.50    spl6_27 <=> ! [X1,X0] : (m1_subset_1(k1_funct_1(sK3,X0),X1) | ~m1_subset_1(X0,sK1) | ~v5_relat_1(sK3,X1))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.22/0.50  fof(f248,plain,(
% 0.22/0.50    m1_subset_1(k1_funct_1(sK3,sK5),sK0) | (~spl6_3 | ~spl6_6 | ~spl6_27)),
% 0.22/0.50    inference(resolution,[],[f225,f110])).
% 0.22/0.50  fof(f225,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | m1_subset_1(k1_funct_1(sK3,sK5),X0)) ) | (~spl6_3 | ~spl6_27)),
% 0.22/0.50    inference(resolution,[],[f224,f79])).
% 0.22/0.50  fof(f224,plain,(
% 0.22/0.50    ( ! [X0] : (~v5_relat_1(sK3,X0) | m1_subset_1(k1_funct_1(sK3,sK5),X0)) ) | (~spl6_3 | ~spl6_27)),
% 0.22/0.50    inference(resolution,[],[f222,f98])).
% 0.22/0.50  fof(f222,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1)) ) | ~spl6_27),
% 0.22/0.50    inference(avatar_component_clause,[],[f221])).
% 0.22/0.50  fof(f239,plain,(
% 0.22/0.50    ~spl6_6 | spl6_16),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f238])).
% 0.22/0.50  fof(f238,plain,(
% 0.22/0.50    $false | (~spl6_6 | spl6_16)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f237])).
% 0.22/0.50  fof(f237,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_16),
% 0.22/0.50    inference(resolution,[],[f166,f75])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f34])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.50    inference(ennf_transformation,[],[f5])).
% 0.22/0.50  fof(f5,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.50  fof(f166,plain,(
% 0.22/0.50    ~v1_relat_1(sK3) | spl6_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f165])).
% 0.22/0.50  fof(f236,plain,(
% 0.22/0.50    ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f231,f175,f101,f105,f109,f113,f117])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl6_18 <=> v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.22/0.50  fof(f231,plain,(
% 0.22/0.50    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | spl6_18),
% 0.22/0.50    inference(resolution,[],[f84,f176])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | spl6_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f175])).
% 0.22/0.50  fof(f84,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (v1_funct_1(k8_funct_2(X0,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f45])).
% 0.22/0.50  fof(f223,plain,(
% 0.22/0.50    spl6_9 | spl6_27 | ~spl6_25),
% 0.22/0.50    inference(avatar_split_clause,[],[f219,f203,f221,f121])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    spl6_25 <=> ! [X5,X4] : (~r2_hidden(X4,sK1) | m1_subset_1(k1_funct_1(sK3,X4),X5) | ~v5_relat_1(sK3,X5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.22/0.50  fof(f219,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(k1_funct_1(sK3,X0),X1) | ~v5_relat_1(sK3,X1) | v1_xboole_0(sK1) | ~m1_subset_1(X0,sK1)) ) | ~spl6_25),
% 0.22/0.50    inference(resolution,[],[f204,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f27])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.22/0.50  fof(f204,plain,(
% 0.22/0.50    ( ! [X4,X5] : (~r2_hidden(X4,sK1) | m1_subset_1(k1_funct_1(sK3,X4),X5) | ~v5_relat_1(sK3,X5)) ) | ~spl6_25),
% 0.22/0.50    inference(avatar_component_clause,[],[f203])).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    ~spl6_6 | ~spl6_24),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f206])).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    $false | (~spl6_6 | ~spl6_24)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f201])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ( ! [X6,X7] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl6_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl6_24 <=> ! [X7,X6] : ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl6_24 | spl6_25 | ~spl6_8 | ~spl6_13),
% 0.22/0.50    inference(avatar_split_clause,[],[f198,f147,f117,f203,f200])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl6_13 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,sK1) | ~v5_relat_1(sK3,X5) | m1_subset_1(k1_funct_1(sK3,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | (~spl6_8 | ~spl6_13)),
% 0.22/0.50    inference(forward_demodulation,[],[f189,f148])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    sK1 = k1_relat_1(sK3) | ~spl6_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f147])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X6,X4,X7,X5] : (~r2_hidden(X4,k1_relat_1(sK3)) | ~v5_relat_1(sK3,X5) | m1_subset_1(k1_funct_1(sK3,X4),X5) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))) ) | ~spl6_8),
% 0.22/0.50    inference(resolution,[],[f134,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    v1_funct_1(sK3) | ~spl6_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f117])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v5_relat_1(X1,X2) | m1_subset_1(k1_funct_1(X1,X0),X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 0.22/0.50    inference(resolution,[],[f82,f75])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | m1_subset_1(k1_funct_1(X2,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2))),
% 0.22/0.50    inference(flattening,[],[f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(k1_funct_1(X2,X1),X0) | ~r2_hidden(X1,k1_relat_1(X2))) | (~v1_funct_1(X2) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((v1_funct_1(X2) & v5_relat_1(X2,X0) & v1_relat_1(X2)) => (r2_hidden(X1,k1_relat_1(X2)) => m1_subset_1(k1_funct_1(X2,X1),X0)))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_funct_1)).
% 0.22/0.50  fof(f187,plain,(
% 0.22/0.50    spl6_9 | ~spl6_18 | ~spl6_19 | ~spl6_20 | ~spl6_3 | ~spl6_21 | spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f172,f89,f185,f97,f181,f178,f175,f121])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    spl6_1 <=> k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) = k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) != k1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) | ~m1_subset_1(sK5,sK1) | ~m1_subset_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK1,sK2) | ~v1_funct_1(k8_funct_2(sK1,sK0,sK2,sK3,sK4)) | v1_xboole_0(sK1) | spl6_1),
% 0.22/0.50    inference(superposition,[],[f90,f83])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) | spl6_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f89])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    ~spl6_7 | spl6_10 | ~spl6_6 | ~spl6_15),
% 0.22/0.50    inference(avatar_split_clause,[],[f159,f156,f109,f125,f113])).
% 0.22/0.50  fof(f156,plain,(
% 0.22/0.50    spl6_15 <=> ! [X0] : (~v1_funct_2(sK3,sK1,X0) | v1_xboole_0(X0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    v1_xboole_0(sK0) | ~v1_funct_2(sK3,sK1,sK0) | (~spl6_6 | ~spl6_15)),
% 0.22/0.50    inference(resolution,[],[f157,f110])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | v1_xboole_0(X0) | ~v1_funct_2(sK3,sK1,X0)) ) | ~spl6_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f156])).
% 0.22/0.50  fof(f158,plain,(
% 0.22/0.50    ~spl6_8 | spl6_15 | spl6_14),
% 0.22/0.50    inference(avatar_split_clause,[],[f153,f150,f156,f117])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    spl6_14 <=> v1_partfun1(sK3,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    ( ! [X0] : (~v1_funct_2(sK3,sK1,X0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | v1_xboole_0(X0)) ) | spl6_14),
% 0.22/0.50    inference(resolution,[],[f151,f67])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(flattening,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    ~v1_partfun1(sK3,sK1) | spl6_14),
% 0.22/0.50    inference(avatar_component_clause,[],[f150])).
% 0.22/0.50  fof(f152,plain,(
% 0.22/0.50    spl6_13 | ~spl6_14 | ~spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f145,f109,f150,f147])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    ~v1_partfun1(sK3,sK1) | sK1 = k1_relat_1(sK3) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f137,f110])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_partfun1(sK3,X2) | k1_relat_1(sK3) = X2) ) | ~spl6_6),
% 0.22/0.50    inference(resolution,[],[f135,f110])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X4)))) )),
% 0.22/0.50    inference(resolution,[],[f132,f78])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f37])).
% 0.22/0.50  fof(f132,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~v4_relat_1(X0,X1) | ~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 0.22/0.50    inference(resolution,[],[f72,f75])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(nnf_transformation,[],[f31])).
% 0.22/0.50  % (14414)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.50    inference(flattening,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl6_12 | ~spl6_2 | ~spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f138,f101,f93,f140])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    ~v1_partfun1(sK4,sK0) | sK0 = k1_relat_1(sK4) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f136,f102])).
% 0.22/0.50  fof(f136,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_partfun1(sK4,X0) | k1_relat_1(sK4) = X0) ) | ~spl6_4),
% 0.22/0.50    inference(resolution,[],[f135,f102])).
% 0.22/0.50  fof(f131,plain,(
% 0.22/0.50    spl6_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f64,f129])).
% 0.22/0.50  fof(f129,plain,(
% 0.22/0.50    spl6_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    v1_xboole_0(k1_xboole_0)),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    ~spl6_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f54,f125])).
% 0.22/0.50  fof(f54,plain,(
% 0.22/0.50    ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ((((k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f50,f49,f48,f47,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ? [X1] : (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) & v1_funct_2(X3,X1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) => (? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & ~v1_xboole_0(sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ? [X3,X2] : (? [X4] : (? [X5] : (k3_funct_2(sK1,X2,k8_funct_2(sK1,sK0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(sK1,sK0,X3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ? [X4] : (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,X4),X5) != k7_partfun1(sK2,X4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(X4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(X4)) => (? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) & v1_funct_1(sK4))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ? [X5] : (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),X5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,X5)) & v1_partfun1(sK4,sK0) & m1_subset_1(X5,sK1)) => (k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5)) & v1_partfun1(sK4,sK0) & m1_subset_1(sK5,sK1))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : (k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0) & m1_subset_1(X5,X1)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2,X3] : (? [X4] : (? [X5] : ((k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) != k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5)) & v1_partfun1(X4,X0)) & m1_subset_1(X5,X1)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,negated_conjecture,(
% 0.22/0.50    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f17])).
% 0.22/0.50  fof(f17,conjecture,(
% 0.22/0.50    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_1(X4)) => ! [X5] : (m1_subset_1(X5,X1) => (v1_partfun1(X4,X0) => k3_funct_2(X1,X2,k8_funct_2(X1,X0,X2,X3,X4),X5) = k7_partfun1(X2,X4,k3_funct_2(X1,X0,X3,X5))))))))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t193_funct_2)).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~spl6_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f55,f121])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    ~v1_xboole_0(sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    spl6_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f56,f117])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    v1_funct_1(sK3)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    spl6_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f57,f113])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    spl6_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f58,f109])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    spl6_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f59,f105])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    v1_funct_1(sK4)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    spl6_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f60,f101])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl6_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f61,f97])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    m1_subset_1(sK5,sK1)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f95,plain,(
% 0.22/0.50    spl6_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f62,f93])).
% 0.22/0.50  fof(f62,plain,(
% 0.22/0.50    v1_partfun1(sK4,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~spl6_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f63,f89])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    k3_funct_2(sK1,sK2,k8_funct_2(sK1,sK0,sK2,sK3,sK4),sK5) != k7_partfun1(sK2,sK4,k3_funct_2(sK1,sK0,sK3,sK5))),
% 0.22/0.50    inference(cnf_transformation,[],[f51])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (14405)------------------------------
% 0.22/0.50  % (14405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (14405)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (14405)Memory used [KB]: 11001
% 0.22/0.50  % (14405)Time elapsed: 0.082 s
% 0.22/0.50  % (14405)------------------------------
% 0.22/0.50  % (14405)------------------------------
% 0.22/0.51  % (14404)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (14398)Success in time 0.145 s
%------------------------------------------------------------------------------
