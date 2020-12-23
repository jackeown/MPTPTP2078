%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:46 EST 2020

% Result     : Theorem 3.72s
% Output     : Refutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :  287 ( 629 expanded)
%              Number of leaves         :   64 ( 242 expanded)
%              Depth                    :   10
%              Number of atoms          :  834 (2167 expanded)
%              Number of equality atoms :  122 ( 521 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f135,f139,f146,f210,f212,f228,f233,f236,f304,f327,f332,f404,f408,f429,f705,f707,f710,f712,f723,f725,f1128,f1185,f1216,f1288,f1308,f1317,f1323,f1336,f1356,f1377,f2955,f3034,f3048,f3055,f3073,f3082,f3155,f4136,f4168,f4234])).

fof(f4234,plain,(
    ~ spl4_396 ),
    inference(avatar_contradiction_clause,[],[f4182])).

fof(f4182,plain,
    ( $false
    | ~ spl4_396 ),
    inference(subsumption_resolution,[],[f60,f4128])).

fof(f4128,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_396 ),
    inference(avatar_component_clause,[],[f4126])).

fof(f4126,plain,
    ( spl4_396
  <=> sK3 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_396])])).

fof(f60,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
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

fof(f4168,plain,
    ( ~ spl4_1
    | spl4_395 ),
    inference(avatar_contradiction_clause,[],[f4166])).

fof(f4166,plain,
    ( $false
    | ~ spl4_1
    | spl4_395 ),
    inference(unit_resulting_resolution,[],[f121,f156,f4124,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f4124,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK1)
    | spl4_395 ),
    inference(avatar_component_clause,[],[f4122])).

fof(f4122,plain,
    ( spl4_395
  <=> r1_tarski(k1_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_395])])).

fof(f156,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f91,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f27])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f121,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f4136,plain,
    ( ~ spl4_1
    | ~ spl4_395
    | spl4_396
    | ~ spl4_314
    | ~ spl4_325 ),
    inference(avatar_split_clause,[],[f4110,f3152,f3045,f4126,f4122,f119])).

fof(f3045,plain,
    ( spl4_314
  <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).

fof(f3152,plain,
    ( spl4_325
  <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_325])])).

fof(f4110,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3)
    | ~ spl4_314
    | ~ spl4_325 ),
    inference(superposition,[],[f105,f4107])).

fof(f4107,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_314
    | ~ spl4_325 ),
    inference(forward_demodulation,[],[f3047,f3154])).

fof(f3154,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ spl4_325 ),
    inference(avatar_component_clause,[],[f3152])).

fof(f3047,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_314 ),
    inference(avatar_component_clause,[],[f3045])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f84,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

fof(f3155,plain,
    ( ~ spl4_3
    | ~ spl4_51
    | ~ spl4_52
    | ~ spl4_53
    | spl4_325
    | ~ spl4_317 ),
    inference(avatar_split_clause,[],[f3118,f3070,f3152,f682,f678,f674,f128])).

fof(f128,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f674,plain,
    ( spl4_51
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f678,plain,
    ( spl4_52
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f682,plain,
    ( spl4_53
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).

fof(f3070,plain,
    ( spl4_317
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_317])])).

fof(f3118,plain,
    ( k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_317 ),
    inference(superposition,[],[f194,f3072])).

fof(f3072,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_317 ),
    inference(avatar_component_clause,[],[f3070])).

fof(f194,plain,(
    ! [X3] :
      ( k2_funct_1(X3) = k5_relat_1(k2_funct_1(X3),k6_partfun1(k1_relat_1(X3)))
      | ~ v1_relat_1(k2_funct_1(X3))
      | ~ v1_funct_1(X3)
      | ~ v2_funct_1(X3)
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f102,f80])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f102,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f64])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f3082,plain,(
    spl4_316 ),
    inference(avatar_contradiction_clause,[],[f3079])).

fof(f3079,plain,
    ( $false
    | spl4_316 ),
    inference(subsumption_resolution,[],[f157,f3068])).

fof(f3068,plain,
    ( ~ v4_relat_1(sK2,sK0)
    | spl4_316 ),
    inference(avatar_component_clause,[],[f3066])).

fof(f3066,plain,
    ( spl4_316
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_316])])).

fof(f157,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f91,f63])).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f3073,plain,
    ( ~ spl4_316
    | ~ spl4_3
    | spl4_317
    | ~ spl4_311 ),
    inference(avatar_split_clause,[],[f3063,f3031,f3070,f128,f3066])).

fof(f3031,plain,
    ( spl4_311
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_311])])).

fof(f3063,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_311 ),
    inference(resolution,[],[f3033,f155])).

fof(f155,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X2))
      | k1_relat_1(X2) = X1
      | ~ v1_relat_1(X2)
      | ~ v4_relat_1(X2,X1) ) ),
    inference(resolution,[],[f89,f86])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3033,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_311 ),
    inference(avatar_component_clause,[],[f3031])).

fof(f3055,plain,
    ( ~ spl4_1
    | spl4_310 ),
    inference(avatar_contradiction_clause,[],[f3053])).

fof(f3053,plain,
    ( $false
    | ~ spl4_1
    | spl4_310 ),
    inference(unit_resulting_resolution,[],[f121,f3029,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f3029,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_310 ),
    inference(avatar_component_clause,[],[f3027])).

fof(f3027,plain,
    ( spl4_310
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).

fof(f3048,plain,
    ( ~ spl4_51
    | ~ spl4_52
    | ~ spl4_53
    | ~ spl4_1
    | ~ spl4_3
    | spl4_314
    | ~ spl4_6
    | ~ spl4_135 ),
    inference(avatar_split_clause,[],[f3043,f1285,f206,f3045,f128,f119,f682,f678,f674])).

fof(f206,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1285,plain,
    ( spl4_135
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f3043,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_6
    | ~ spl4_135 ),
    inference(forward_demodulation,[],[f3000,f208])).

fof(f208,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f206])).

fof(f3000,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ spl4_135 ),
    inference(superposition,[],[f477,f1287])).

fof(f1287,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1285])).

fof(f477,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f452])).

fof(f452,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f75,f103])).

fof(f103,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f82,f64])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f3034,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | ~ spl4_310
    | ~ spl4_8
    | spl4_311
    | ~ spl4_135
    | ~ spl4_140 ),
    inference(avatar_split_clause,[],[f3025,f1329,f1285,f3031,f221,f3027,f119,f128])).

fof(f221,plain,
    ( spl4_8
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f1329,plain,
    ( spl4_140
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).

fof(f3025,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_135
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f3024,f100])).

fof(f100,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f3024,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_135
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f3023,f98])).

fof(f98,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f65,f64,f64])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f3023,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(sK0))),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_135
    | ~ spl4_140 ),
    inference(forward_demodulation,[],[f2997,f1331])).

fof(f1331,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_140 ),
    inference(avatar_component_clause,[],[f1329])).

fof(f2997,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(sK0))),k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_135 ),
    inference(superposition,[],[f243,f1287])).

fof(f243,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f73,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f2955,plain,(
    spl4_134 ),
    inference(avatar_contradiction_clause,[],[f2917])).

fof(f2917,plain,
    ( $false
    | spl4_134 ),
    inference(unit_resulting_resolution,[],[f61,f52,f54,f63,f1283,f721])).

fof(f721,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f97,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1283,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_134 ),
    inference(avatar_component_clause,[],[f1281])).

fof(f1281,plain,
    ( spl4_134
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f1377,plain,(
    spl4_143 ),
    inference(avatar_contradiction_clause,[],[f1371])).

fof(f1371,plain,
    ( $false
    | spl4_143 ),
    inference(unit_resulting_resolution,[],[f149,f158,f1355,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(k6_partfun1(X0),X1)
      | ~ v1_relat_1(k6_partfun1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f86,f101])).

fof(f101,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f1355,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | spl4_143 ),
    inference(avatar_component_clause,[],[f1353])).

fof(f1353,plain,
    ( spl4_143
  <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).

fof(f158,plain,(
    ! [X0] : v4_relat_1(k6_partfun1(X0),X0) ),
    inference(resolution,[],[f91,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f66,f64])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f149,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(resolution,[],[f117,f83])).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f117,plain,(
    ! [X0] :
      ( ~ v1_relat_1(k2_zfmisc_1(X0,X0))
      | v1_relat_1(k6_partfun1(X0)) ) ),
    inference(resolution,[],[f76,f99])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f1356,plain,
    ( ~ spl4_3
    | ~ spl4_143
    | spl4_141 ),
    inference(avatar_split_clause,[],[f1346,f1333,f1353,f128])).

fof(f1333,plain,
    ( spl4_141
  <=> r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).

fof(f1346,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | spl4_141 ),
    inference(superposition,[],[f1335,f72])).

fof(f72,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1335,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))
    | spl4_141 ),
    inference(avatar_component_clause,[],[f1333])).

fof(f1336,plain,
    ( spl4_140
    | ~ spl4_141
    | ~ spl4_139 ),
    inference(avatar_split_clause,[],[f1326,f1320,f1333,f1329])).

fof(f1320,plain,
    ( spl4_139
  <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f1326,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))
    | k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl4_139 ),
    inference(resolution,[],[f1322,f89])).

fof(f1322,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_139 ),
    inference(avatar_component_clause,[],[f1320])).

fof(f1323,plain,
    ( ~ spl4_8
    | spl4_139
    | ~ spl4_17
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f1318,f1314,f397,f1320,f221])).

fof(f397,plain,
    ( spl4_17
  <=> v1_relat_1(k4_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f1314,plain,
    ( spl4_138
  <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f1318,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_138 ),
    inference(resolution,[],[f1316,f152])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ v4_relat_1(k4_relat_1(X2),X3)
      | ~ v1_relat_1(k4_relat_1(X2))
      | r1_tarski(k2_relat_1(X2),X3)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f86,f71])).

fof(f71,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1316,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f1314])).

fof(f1317,plain,
    ( ~ spl4_3
    | spl4_138
    | ~ spl4_137 ),
    inference(avatar_split_clause,[],[f1312,f1305,f1314,f128])).

fof(f1305,plain,
    ( spl4_137
  <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f1312,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_137 ),
    inference(superposition,[],[f1307,f72])).

fof(f1307,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ spl4_137 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f1308,plain,
    ( ~ spl4_3
    | ~ spl4_19
    | spl4_137
    | ~ spl4_10
    | ~ spl4_117 ),
    inference(avatar_split_clause,[],[f1303,f1182,f230,f1305,f412,f128])).

fof(f412,plain,
    ( spl4_19
  <=> v1_relat_1(k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f230,plain,
    ( spl4_10
  <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f1182,plain,
    ( spl4_117
  <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).

fof(f1303,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_10
    | ~ spl4_117 ),
    inference(forward_demodulation,[],[f1296,f232])).

fof(f232,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f1296,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(k5_relat_1(sK2,k6_partfun1(sK1)))))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_117 ),
    inference(superposition,[],[f1184,f241])).

fof(f241,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X1,k6_partfun1(X0))) = k5_relat_1(k6_partfun1(X0),k4_relat_1(X1))
      | ~ v1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f74,f98])).

fof(f1184,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))))
    | ~ spl4_117 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1288,plain,
    ( ~ spl4_134
    | spl4_135
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f1269,f702,f1285,f1281])).

fof(f702,plain,
    ( spl4_57
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f1269,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_57 ),
    inference(resolution,[],[f532,f704])).

fof(f704,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f702])).

fof(f532,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f94,f99])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1216,plain,
    ( ~ spl4_3
    | ~ spl4_19
    | ~ spl4_8
    | ~ spl4_10
    | spl4_112 ),
    inference(avatar_split_clause,[],[f1215,f1159,f230,f221,f412,f128])).

fof(f1159,plain,
    ( spl4_112
  <=> v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).

fof(f1215,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_10
    | spl4_112 ),
    inference(forward_demodulation,[],[f1212,f232])).

fof(f1212,plain,
    ( ~ v1_relat_1(k4_relat_1(k5_relat_1(sK2,k6_partfun1(sK1))))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | spl4_112 ),
    inference(superposition,[],[f1161,f241])).

fof(f1161,plain,
    ( ~ v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))
    | spl4_112 ),
    inference(avatar_component_clause,[],[f1159])).

fof(f1185,plain,
    ( ~ spl4_112
    | ~ spl4_17
    | spl4_117
    | ~ spl4_108 ),
    inference(avatar_split_clause,[],[f1151,f1119,f1182,f397,f1159])).

fof(f1119,plain,
    ( spl4_108
  <=> k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).

fof(f1151,plain,
    ( v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))))
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))
    | ~ spl4_108 ),
    inference(superposition,[],[f148,f1121])).

fof(f1121,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))
    | ~ spl4_108 ),
    inference(avatar_component_clause,[],[f1119])).

fof(f148,plain,(
    ! [X1] :
      ( v4_relat_1(k4_relat_1(X1),k2_relat_1(X1))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f140,f71])).

fof(f140,plain,(
    ! [X0] :
      ( v4_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f85,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1128,plain,
    ( ~ spl4_19
    | ~ spl4_8
    | spl4_108
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f1101,f401,f1119,f221,f412])).

fof(f401,plain,
    ( spl4_18
  <=> k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f1101,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(k6_partfun1(sK1))
    | ~ spl4_18 ),
    inference(superposition,[],[f403,f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k4_relat_1(X1),k6_partfun1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k6_partfun1(X0)) ) ),
    inference(superposition,[],[f74,f98])).

fof(f403,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f401])).

fof(f725,plain,(
    spl4_56 ),
    inference(avatar_contradiction_clause,[],[f724])).

fof(f724,plain,
    ( $false
    | spl4_56 ),
    inference(subsumption_resolution,[],[f52,f700])).

fof(f700,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_56 ),
    inference(avatar_component_clause,[],[f698])).

fof(f698,plain,
    ( spl4_56
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f723,plain,(
    spl4_55 ),
    inference(avatar_contradiction_clause,[],[f722])).

fof(f722,plain,
    ( $false
    | spl4_55 ),
    inference(subsumption_resolution,[],[f54,f696])).

fof(f696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_55 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_55
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f712,plain,(
    spl4_51 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl4_51 ),
    inference(subsumption_resolution,[],[f57,f676])).

fof(f676,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_51 ),
    inference(avatar_component_clause,[],[f674])).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f710,plain,
    ( ~ spl4_3
    | spl4_53 ),
    inference(avatar_contradiction_clause,[],[f708])).

fof(f708,plain,
    ( $false
    | ~ spl4_3
    | spl4_53 ),
    inference(unit_resulting_resolution,[],[f130,f61,f684,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f684,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_53 ),
    inference(avatar_component_clause,[],[f682])).

fof(f130,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f128])).

fof(f707,plain,(
    spl4_52 ),
    inference(avatar_contradiction_clause,[],[f706])).

fof(f706,plain,
    ( $false
    | spl4_52 ),
    inference(subsumption_resolution,[],[f61,f680])).

fof(f680,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_52 ),
    inference(avatar_component_clause,[],[f678])).

fof(f705,plain,
    ( ~ spl4_52
    | ~ spl4_55
    | ~ spl4_56
    | ~ spl4_5
    | spl4_57 ),
    inference(avatar_split_clause,[],[f690,f702,f202,f698,f694,f678])).

fof(f202,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f690,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f56,f95])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f429,plain,(
    spl4_19 ),
    inference(avatar_contradiction_clause,[],[f424])).

fof(f424,plain,
    ( $false
    | spl4_19 ),
    inference(unit_resulting_resolution,[],[f83,f99,f414,f76])).

fof(f414,plain,
    ( ~ v1_relat_1(k6_partfun1(sK1))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f412])).

fof(f408,plain,
    ( ~ spl4_8
    | spl4_17 ),
    inference(avatar_contradiction_clause,[],[f406])).

fof(f406,plain,
    ( $false
    | ~ spl4_8
    | spl4_17 ),
    inference(unit_resulting_resolution,[],[f222,f399,f69])).

fof(f399,plain,
    ( ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f397])).

fof(f222,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f404,plain,
    ( ~ spl4_8
    | ~ spl4_17
    | spl4_18
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f387,f320,f401,f397,f221])).

fof(f320,plain,
    ( spl4_13
  <=> sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f387,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1))
    | ~ v1_relat_1(k4_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_13 ),
    inference(superposition,[],[f163,f322])).

fof(f322,plain,
    ( sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f320])).

fof(f163,plain,(
    ! [X1] :
      ( k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_partfun1(k1_relat_1(X1)))
      | ~ v1_relat_1(k4_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f102,f72])).

fof(f332,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | spl4_14 ),
    inference(avatar_contradiction_clause,[],[f329])).

fof(f329,plain,
    ( $false
    | ~ spl4_8
    | ~ spl4_9
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f222,f227,f326,f86])).

fof(f326,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | spl4_14 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl4_14
  <=> r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f227,plain,
    ( v4_relat_1(k4_relat_1(sK2),sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_9
  <=> v4_relat_1(k4_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f327,plain,
    ( spl4_13
    | ~ spl4_14
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f317,f301,f324,f320])).

fof(f301,plain,
    ( spl4_12
  <=> r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f317,plain,
    ( ~ r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)
    | sK1 = k1_relat_1(k4_relat_1(sK2))
    | ~ spl4_12 ),
    inference(resolution,[],[f303,f89])).

fof(f303,plain,
    ( r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f301])).

fof(f304,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | spl4_12
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f292,f206,f301,f221,f128])).

fof(f292,plain,
    ( r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f282,f208])).

fof(f282,plain,(
    ! [X2] :
      ( r1_tarski(k2_relat_1(X2),k1_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(k4_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X2] :
      ( ~ v1_relat_1(k4_relat_1(X2))
      | r1_tarski(k2_relat_1(X2),k1_relat_1(k4_relat_1(X2)))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k4_relat_1(X2)) ) ),
    inference(resolution,[],[f152,f140])).

fof(f236,plain,
    ( ~ spl4_3
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f234])).

fof(f234,plain,
    ( $false
    | ~ spl4_3
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f130,f223,f69])).

fof(f223,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f233,plain,
    ( ~ spl4_3
    | spl4_10
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f215,f206,f230,f128])).

fof(f215,plain,
    ( sK2 = k5_relat_1(sK2,k6_partfun1(sK1))
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f102,f208])).

fof(f228,plain,
    ( ~ spl4_3
    | ~ spl4_8
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f214,f206,f225,f221,f128])).

fof(f214,plain,
    ( v4_relat_1(k4_relat_1(sK2),sK1)
    | ~ v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f148,f208])).

fof(f212,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f63,f204])).

fof(f204,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f202])).

fof(f210,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f200,f206,f202])).

fof(f200,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f55,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f146,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f83,f134])).

fof(f134,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f139,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f83,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f135,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f116,f132,f128])).

fof(f116,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f76,f63])).

fof(f126,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f115,f123,f119])).

fof(f115,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f76,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:06:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.50  % (14933)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (14939)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (14929)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (14949)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (14948)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (14931)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (14958)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (14941)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.33/0.54  % (14930)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.33/0.54  % (14934)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.33/0.54  % (14946)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.33/0.54  % (14932)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.33/0.54  % (14938)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.33/0.55  % (14937)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.33/0.55  % (14950)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.33/0.55  % (14940)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.55  % (14942)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.56  % (14952)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.56  % (14956)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.56  % (14953)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.56  % (14955)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (14951)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.56  % (14944)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.56  % (14947)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.57  % (14943)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.57  % (14945)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.57  % (14954)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.57  % (14945)Refutation not found, incomplete strategy% (14945)------------------------------
% 1.48/0.57  % (14945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (14945)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (14945)Memory used [KB]: 10746
% 1.48/0.57  % (14945)Time elapsed: 0.144 s
% 1.48/0.57  % (14945)------------------------------
% 1.48/0.57  % (14945)------------------------------
% 1.48/0.57  % (14935)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.58  % (14936)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.59  % (14957)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.36/0.68  % (14959)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 3.47/0.83  % (14953)Time limit reached!
% 3.47/0.83  % (14953)------------------------------
% 3.47/0.83  % (14953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.83  % (14953)Termination reason: Time limit
% 3.47/0.83  % (14953)Termination phase: Saturation
% 3.47/0.83  
% 3.47/0.83  % (14953)Memory used [KB]: 13048
% 3.47/0.83  % (14953)Time elapsed: 0.419 s
% 3.47/0.83  % (14953)------------------------------
% 3.47/0.83  % (14953)------------------------------
% 3.47/0.83  % (14931)Time limit reached!
% 3.47/0.83  % (14931)------------------------------
% 3.47/0.83  % (14931)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.47/0.83  % (14931)Termination reason: Time limit
% 3.47/0.83  
% 3.47/0.83  % (14931)Memory used [KB]: 6652
% 3.47/0.83  % (14931)Time elapsed: 0.417 s
% 3.47/0.83  % (14931)------------------------------
% 3.47/0.83  % (14931)------------------------------
% 3.72/0.87  % (14942)Refutation found. Thanks to Tanya!
% 3.72/0.87  % SZS status Theorem for theBenchmark
% 3.72/0.87  % SZS output start Proof for theBenchmark
% 3.72/0.87  fof(f4254,plain,(
% 3.72/0.87    $false),
% 3.72/0.87    inference(avatar_sat_refutation,[],[f126,f135,f139,f146,f210,f212,f228,f233,f236,f304,f327,f332,f404,f408,f429,f705,f707,f710,f712,f723,f725,f1128,f1185,f1216,f1288,f1308,f1317,f1323,f1336,f1356,f1377,f2955,f3034,f3048,f3055,f3073,f3082,f3155,f4136,f4168,f4234])).
% 3.72/0.87  fof(f4234,plain,(
% 3.72/0.87    ~spl4_396),
% 3.72/0.87    inference(avatar_contradiction_clause,[],[f4182])).
% 3.72/0.87  fof(f4182,plain,(
% 3.72/0.87    $false | ~spl4_396),
% 3.72/0.87    inference(subsumption_resolution,[],[f60,f4128])).
% 3.72/0.87  fof(f4128,plain,(
% 3.72/0.87    sK3 = k2_funct_1(sK2) | ~spl4_396),
% 3.72/0.87    inference(avatar_component_clause,[],[f4126])).
% 3.72/0.87  fof(f4126,plain,(
% 3.72/0.87    spl4_396 <=> sK3 = k2_funct_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_396])])).
% 3.72/0.87  fof(f60,plain,(
% 3.72/0.87    sK3 != k2_funct_1(sK2)),
% 3.72/0.87    inference(cnf_transformation,[],[f27])).
% 3.72/0.87  fof(f27,plain,(
% 3.72/0.87    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.72/0.87    inference(flattening,[],[f26])).
% 3.72/0.87  fof(f26,plain,(
% 3.72/0.87    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.72/0.87    inference(ennf_transformation,[],[f25])).
% 3.72/0.87  fof(f25,negated_conjecture,(
% 3.72/0.87    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.72/0.87    inference(negated_conjecture,[],[f24])).
% 3.72/0.87  fof(f24,conjecture,(
% 3.72/0.87    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 3.72/0.87  fof(f4168,plain,(
% 3.72/0.87    ~spl4_1 | spl4_395),
% 3.72/0.87    inference(avatar_contradiction_clause,[],[f4166])).
% 3.72/0.87  fof(f4166,plain,(
% 3.72/0.87    $false | (~spl4_1 | spl4_395)),
% 3.72/0.87    inference(unit_resulting_resolution,[],[f121,f156,f4124,f86])).
% 3.72/0.87  fof(f86,plain,(
% 3.72/0.87    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | ~v4_relat_1(X1,X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f43])).
% 3.72/0.87  fof(f43,plain,(
% 3.72/0.87    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/0.87    inference(ennf_transformation,[],[f3])).
% 3.72/0.87  fof(f3,axiom,(
% 3.72/0.87    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 3.72/0.87  fof(f4124,plain,(
% 3.72/0.87    ~r1_tarski(k1_relat_1(sK3),sK1) | spl4_395),
% 3.72/0.87    inference(avatar_component_clause,[],[f4122])).
% 3.72/0.87  fof(f4122,plain,(
% 3.72/0.87    spl4_395 <=> r1_tarski(k1_relat_1(sK3),sK1)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_395])])).
% 3.72/0.87  fof(f156,plain,(
% 3.72/0.87    v4_relat_1(sK3,sK1)),
% 3.72/0.87    inference(resolution,[],[f91,f54])).
% 3.72/0.87  fof(f54,plain,(
% 3.72/0.87    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.72/0.87    inference(cnf_transformation,[],[f27])).
% 3.72/0.87  fof(f91,plain,(
% 3.72/0.87    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f45])).
% 3.72/0.87  fof(f45,plain,(
% 3.72/0.87    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.87    inference(ennf_transformation,[],[f17])).
% 3.72/0.87  fof(f17,axiom,(
% 3.72/0.87    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.72/0.87  fof(f121,plain,(
% 3.72/0.87    v1_relat_1(sK3) | ~spl4_1),
% 3.72/0.87    inference(avatar_component_clause,[],[f119])).
% 3.72/0.87  fof(f119,plain,(
% 3.72/0.87    spl4_1 <=> v1_relat_1(sK3)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 3.72/0.87  fof(f4136,plain,(
% 3.72/0.87    ~spl4_1 | ~spl4_395 | spl4_396 | ~spl4_314 | ~spl4_325),
% 3.72/0.87    inference(avatar_split_clause,[],[f4110,f3152,f3045,f4126,f4122,f119])).
% 3.72/0.87  fof(f3045,plain,(
% 3.72/0.87    spl4_314 <=> k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_314])])).
% 3.72/0.87  fof(f3152,plain,(
% 3.72/0.87    spl4_325 <=> k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_325])])).
% 3.72/0.87  fof(f4110,plain,(
% 3.72/0.87    sK3 = k2_funct_1(sK2) | ~r1_tarski(k1_relat_1(sK3),sK1) | ~v1_relat_1(sK3) | (~spl4_314 | ~spl4_325)),
% 3.72/0.87    inference(superposition,[],[f105,f4107])).
% 3.72/0.87  fof(f4107,plain,(
% 3.72/0.87    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(sK1),sK3) | (~spl4_314 | ~spl4_325)),
% 3.72/0.87    inference(forward_demodulation,[],[f3047,f3154])).
% 3.72/0.87  fof(f3154,plain,(
% 3.72/0.87    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~spl4_325),
% 3.72/0.87    inference(avatar_component_clause,[],[f3152])).
% 3.72/0.87  fof(f3047,plain,(
% 3.72/0.87    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_314),
% 3.72/0.87    inference(avatar_component_clause,[],[f3045])).
% 3.72/0.87  fof(f105,plain,(
% 3.72/0.87    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.72/0.87    inference(definition_unfolding,[],[f84,f64])).
% 3.72/0.87  fof(f64,plain,(
% 3.72/0.87    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f23])).
% 3.72/0.87  fof(f23,axiom,(
% 3.72/0.87    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 3.72/0.87  fof(f84,plain,(
% 3.72/0.87    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 3.72/0.87    inference(cnf_transformation,[],[f42])).
% 3.72/0.87  fof(f42,plain,(
% 3.72/0.87    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.72/0.87    inference(flattening,[],[f41])).
% 3.72/0.87  fof(f41,plain,(
% 3.72/0.87    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.72/0.87    inference(ennf_transformation,[],[f12])).
% 3.72/0.87  fof(f12,axiom,(
% 3.72/0.87    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).
% 3.72/0.87  fof(f3155,plain,(
% 3.72/0.87    ~spl4_3 | ~spl4_51 | ~spl4_52 | ~spl4_53 | spl4_325 | ~spl4_317),
% 3.72/0.87    inference(avatar_split_clause,[],[f3118,f3070,f3152,f682,f678,f674,f128])).
% 3.72/0.87  fof(f128,plain,(
% 3.72/0.87    spl4_3 <=> v1_relat_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 3.72/0.87  fof(f674,plain,(
% 3.72/0.87    spl4_51 <=> v2_funct_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 3.72/0.87  fof(f678,plain,(
% 3.72/0.87    spl4_52 <=> v1_funct_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 3.72/0.87  fof(f682,plain,(
% 3.72/0.87    spl4_53 <=> v1_relat_1(k2_funct_1(sK2))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_53])])).
% 3.72/0.87  fof(f3070,plain,(
% 3.72/0.87    spl4_317 <=> sK0 = k1_relat_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_317])])).
% 3.72/0.87  fof(f3118,plain,(
% 3.72/0.87    k2_funct_1(sK2) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_317),
% 3.72/0.87    inference(superposition,[],[f194,f3072])).
% 3.72/0.87  fof(f3072,plain,(
% 3.72/0.87    sK0 = k1_relat_1(sK2) | ~spl4_317),
% 3.72/0.87    inference(avatar_component_clause,[],[f3070])).
% 3.72/0.87  fof(f194,plain,(
% 3.72/0.87    ( ! [X3] : (k2_funct_1(X3) = k5_relat_1(k2_funct_1(X3),k6_partfun1(k1_relat_1(X3))) | ~v1_relat_1(k2_funct_1(X3)) | ~v1_funct_1(X3) | ~v2_funct_1(X3) | ~v1_relat_1(X3)) )),
% 3.72/0.87    inference(superposition,[],[f102,f80])).
% 3.72/0.87  fof(f80,plain,(
% 3.72/0.87    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f38])).
% 3.72/0.87  fof(f38,plain,(
% 3.72/0.87    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.87    inference(flattening,[],[f37])).
% 3.72/0.87  fof(f37,plain,(
% 3.72/0.87    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.87    inference(ennf_transformation,[],[f15])).
% 3.72/0.87  fof(f15,axiom,(
% 3.72/0.87    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 3.72/0.87  fof(f102,plain,(
% 3.72/0.87    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(definition_unfolding,[],[f70,f64])).
% 3.72/0.87  fof(f70,plain,(
% 3.72/0.87    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 3.72/0.87    inference(cnf_transformation,[],[f29])).
% 3.72/0.87  fof(f29,plain,(
% 3.72/0.87    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.72/0.87    inference(ennf_transformation,[],[f13])).
% 3.72/0.87  fof(f13,axiom,(
% 3.72/0.87    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 3.72/0.87  fof(f3082,plain,(
% 3.72/0.87    spl4_316),
% 3.72/0.87    inference(avatar_contradiction_clause,[],[f3079])).
% 3.72/0.87  fof(f3079,plain,(
% 3.72/0.87    $false | spl4_316),
% 3.72/0.87    inference(subsumption_resolution,[],[f157,f3068])).
% 3.72/0.87  fof(f3068,plain,(
% 3.72/0.87    ~v4_relat_1(sK2,sK0) | spl4_316),
% 3.72/0.87    inference(avatar_component_clause,[],[f3066])).
% 3.72/0.87  fof(f3066,plain,(
% 3.72/0.87    spl4_316 <=> v4_relat_1(sK2,sK0)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_316])])).
% 3.72/0.87  fof(f157,plain,(
% 3.72/0.87    v4_relat_1(sK2,sK0)),
% 3.72/0.87    inference(resolution,[],[f91,f63])).
% 3.72/0.87  fof(f63,plain,(
% 3.72/0.87    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.72/0.87    inference(cnf_transformation,[],[f27])).
% 3.72/0.87  fof(f3073,plain,(
% 3.72/0.87    ~spl4_316 | ~spl4_3 | spl4_317 | ~spl4_311),
% 3.72/0.87    inference(avatar_split_clause,[],[f3063,f3031,f3070,f128,f3066])).
% 3.72/0.87  fof(f3031,plain,(
% 3.72/0.87    spl4_311 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_311])])).
% 3.72/0.87  fof(f3063,plain,(
% 3.72/0.87    sK0 = k1_relat_1(sK2) | ~v1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_311),
% 3.72/0.87    inference(resolution,[],[f3033,f155])).
% 3.72/0.87  fof(f155,plain,(
% 3.72/0.87    ( ! [X2,X1] : (~r1_tarski(X1,k1_relat_1(X2)) | k1_relat_1(X2) = X1 | ~v1_relat_1(X2) | ~v4_relat_1(X2,X1)) )),
% 3.72/0.87    inference(resolution,[],[f89,f86])).
% 3.72/0.87  fof(f89,plain,(
% 3.72/0.87    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 3.72/0.87    inference(cnf_transformation,[],[f1])).
% 3.72/0.87  fof(f1,axiom,(
% 3.72/0.87    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.72/0.87  fof(f3033,plain,(
% 3.72/0.87    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_311),
% 3.72/0.87    inference(avatar_component_clause,[],[f3031])).
% 3.72/0.87  fof(f3055,plain,(
% 3.72/0.87    ~spl4_1 | spl4_310),
% 3.72/0.87    inference(avatar_contradiction_clause,[],[f3053])).
% 3.72/0.87  fof(f3053,plain,(
% 3.72/0.87    $false | (~spl4_1 | spl4_310)),
% 3.72/0.87    inference(unit_resulting_resolution,[],[f121,f3029,f69])).
% 3.72/0.87  fof(f69,plain,(
% 3.72/0.87    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f28])).
% 3.72/0.87  fof(f28,plain,(
% 3.72/0.87    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.72/0.87    inference(ennf_transformation,[],[f4])).
% 3.72/0.87  fof(f4,axiom,(
% 3.72/0.87    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 3.72/0.87  fof(f3029,plain,(
% 3.72/0.87    ~v1_relat_1(k4_relat_1(sK3)) | spl4_310),
% 3.72/0.87    inference(avatar_component_clause,[],[f3027])).
% 3.72/0.87  fof(f3027,plain,(
% 3.72/0.87    spl4_310 <=> v1_relat_1(k4_relat_1(sK3))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_310])])).
% 3.72/0.87  fof(f3048,plain,(
% 3.72/0.87    ~spl4_51 | ~spl4_52 | ~spl4_53 | ~spl4_1 | ~spl4_3 | spl4_314 | ~spl4_6 | ~spl4_135),
% 3.72/0.87    inference(avatar_split_clause,[],[f3043,f1285,f206,f3045,f128,f119,f682,f678,f674])).
% 3.72/0.87  fof(f206,plain,(
% 3.72/0.87    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 3.72/0.87  fof(f1285,plain,(
% 3.72/0.87    spl4_135 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).
% 3.72/0.87  fof(f3043,plain,(
% 3.72/0.87    k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | (~spl4_6 | ~spl4_135)),
% 3.72/0.87    inference(forward_demodulation,[],[f3000,f208])).
% 3.72/0.87  fof(f208,plain,(
% 3.72/0.87    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 3.72/0.87    inference(avatar_component_clause,[],[f206])).
% 3.72/0.87  fof(f3000,plain,(
% 3.72/0.87    k5_relat_1(k6_partfun1(k2_relat_1(sK2)),sK3) = k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~spl4_135),
% 3.72/0.87    inference(superposition,[],[f477,f1287])).
% 3.72/0.87  fof(f1287,plain,(
% 3.72/0.87    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_135),
% 3.72/0.87    inference(avatar_component_clause,[],[f1285])).
% 3.72/0.87  fof(f477,plain,(
% 3.72/0.87    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0)) )),
% 3.72/0.87    inference(duplicate_literal_removal,[],[f452])).
% 3.72/0.87  fof(f452,plain,(
% 3.72/0.87    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X0),k5_relat_1(X0,X1)) = k5_relat_1(k6_partfun1(k2_relat_1(X0)),X1) | ~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(superposition,[],[f75,f103])).
% 3.72/0.87  fof(f103,plain,(
% 3.72/0.87    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(definition_unfolding,[],[f82,f64])).
% 3.72/0.87  fof(f82,plain,(
% 3.72/0.87    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f40])).
% 3.72/0.87  fof(f40,plain,(
% 3.72/0.87    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.87    inference(flattening,[],[f39])).
% 3.72/0.87  fof(f39,plain,(
% 3.72/0.87    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.87    inference(ennf_transformation,[],[f16])).
% 3.72/0.87  fof(f16,axiom,(
% 3.72/0.87    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 3.72/0.87  fof(f75,plain,(
% 3.72/0.87    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f33])).
% 3.72/0.87  fof(f33,plain,(
% 3.72/0.87    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.87    inference(ennf_transformation,[],[f9])).
% 3.72/0.87  fof(f9,axiom,(
% 3.72/0.87    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 3.72/0.87  fof(f3034,plain,(
% 3.72/0.87    ~spl4_3 | ~spl4_1 | ~spl4_310 | ~spl4_8 | spl4_311 | ~spl4_135 | ~spl4_140),
% 3.72/0.87    inference(avatar_split_clause,[],[f3025,f1329,f1285,f3031,f221,f3027,f119,f128])).
% 3.72/0.87  fof(f221,plain,(
% 3.72/0.87    spl4_8 <=> v1_relat_1(k4_relat_1(sK2))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 3.72/0.87  fof(f1329,plain,(
% 3.72/0.87    spl4_140 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 3.72/0.87    introduced(avatar_definition,[new_symbols(naming,[spl4_140])])).
% 3.72/0.87  fof(f3025,plain,(
% 3.72/0.87    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_135 | ~spl4_140)),
% 3.72/0.87    inference(forward_demodulation,[],[f3024,f100])).
% 3.72/0.87  fof(f100,plain,(
% 3.72/0.87    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.72/0.87    inference(definition_unfolding,[],[f68,f64])).
% 3.72/0.87  fof(f68,plain,(
% 3.72/0.87    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.87    inference(cnf_transformation,[],[f10])).
% 3.72/0.87  fof(f10,axiom,(
% 3.72/0.87    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 3.72/0.87  fof(f3024,plain,(
% 3.72/0.87    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_135 | ~spl4_140)),
% 3.72/0.87    inference(forward_demodulation,[],[f3023,f98])).
% 3.72/0.87  fof(f98,plain,(
% 3.72/0.87    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 3.72/0.87    inference(definition_unfolding,[],[f65,f64,f64])).
% 3.72/0.87  fof(f65,plain,(
% 3.72/0.87    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 3.72/0.87    inference(cnf_transformation,[],[f11])).
% 3.72/0.87  fof(f11,axiom,(
% 3.72/0.87    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 3.72/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 3.72/0.87  fof(f3023,plain,(
% 3.72/0.87    r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(sK0))),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_135 | ~spl4_140)),
% 3.72/0.87    inference(forward_demodulation,[],[f2997,f1331])).
% 3.72/0.87  fof(f1331,plain,(
% 3.72/0.87    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl4_140),
% 3.72/0.87    inference(avatar_component_clause,[],[f1329])).
% 3.72/0.87  fof(f2997,plain,(
% 3.72/0.87    r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(sK0))),k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_135),
% 3.72/0.87    inference(superposition,[],[f243,f1287])).
% 3.72/0.87  fof(f243,plain,(
% 3.72/0.87    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(X1,X0))),k2_relat_1(k4_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(X1)) )),
% 3.72/0.87    inference(superposition,[],[f73,f74])).
% 3.72/0.87  fof(f74,plain,(
% 3.72/0.87    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.72/0.87    inference(cnf_transformation,[],[f32])).
% 3.72/0.87  fof(f32,plain,(
% 3.72/0.87    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f8])).
% 3.72/0.88  fof(f8,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 3.72/0.88  fof(f73,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f31])).
% 3.72/0.88  fof(f31,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f7])).
% 3.72/0.88  fof(f7,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 3.72/0.88  fof(f2955,plain,(
% 3.72/0.88    spl4_134),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f2917])).
% 3.72/0.88  fof(f2917,plain,(
% 3.72/0.88    $false | spl4_134),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f61,f52,f54,f63,f1283,f721])).
% 3.72/0.88  fof(f721,plain,(
% 3.72/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 3.72/0.88    inference(duplicate_literal_removal,[],[f720])).
% 3.72/0.88  fof(f720,plain,(
% 3.72/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 3.72/0.88    inference(superposition,[],[f97,f95])).
% 3.72/0.88  fof(f95,plain,(
% 3.72/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f49])).
% 3.72/0.88  fof(f49,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.88    inference(flattening,[],[f48])).
% 3.72/0.88  fof(f48,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.88    inference(ennf_transformation,[],[f22])).
% 3.72/0.88  fof(f22,axiom,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 3.72/0.88  fof(f97,plain,(
% 3.72/0.88    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f51])).
% 3.72/0.88  fof(f51,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.72/0.88    inference(flattening,[],[f50])).
% 3.72/0.88  fof(f50,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.72/0.88    inference(ennf_transformation,[],[f21])).
% 3.72/0.88  fof(f21,axiom,(
% 3.72/0.88    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 3.72/0.88  fof(f1283,plain,(
% 3.72/0.88    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_134),
% 3.72/0.88    inference(avatar_component_clause,[],[f1281])).
% 3.72/0.88  fof(f1281,plain,(
% 3.72/0.88    spl4_134 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 3.72/0.88  fof(f52,plain,(
% 3.72/0.88    v1_funct_1(sK3)),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  fof(f61,plain,(
% 3.72/0.88    v1_funct_1(sK2)),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  fof(f1377,plain,(
% 3.72/0.88    spl4_143),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f1371])).
% 3.72/0.88  fof(f1371,plain,(
% 3.72/0.88    $false | spl4_143),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f149,f158,f1355,f151])).
% 3.72/0.88  fof(f151,plain,(
% 3.72/0.88    ( ! [X0,X1] : (~v4_relat_1(k6_partfun1(X0),X1) | ~v1_relat_1(k6_partfun1(X0)) | r1_tarski(X0,X1)) )),
% 3.72/0.88    inference(superposition,[],[f86,f101])).
% 3.72/0.88  fof(f101,plain,(
% 3.72/0.88    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.72/0.88    inference(definition_unfolding,[],[f67,f64])).
% 3.72/0.88  fof(f67,plain,(
% 3.72/0.88    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.72/0.88    inference(cnf_transformation,[],[f10])).
% 3.72/0.88  fof(f1355,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | spl4_143),
% 3.72/0.88    inference(avatar_component_clause,[],[f1353])).
% 3.72/0.88  fof(f1353,plain,(
% 3.72/0.88    spl4_143 <=> r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_143])])).
% 3.72/0.88  fof(f158,plain,(
% 3.72/0.88    ( ! [X0] : (v4_relat_1(k6_partfun1(X0),X0)) )),
% 3.72/0.88    inference(resolution,[],[f91,f99])).
% 3.72/0.88  fof(f99,plain,(
% 3.72/0.88    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.72/0.88    inference(definition_unfolding,[],[f66,f64])).
% 3.72/0.88  fof(f66,plain,(
% 3.72/0.88    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f20])).
% 3.72/0.88  fof(f20,axiom,(
% 3.72/0.88    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 3.72/0.88  fof(f149,plain,(
% 3.72/0.88    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.72/0.88    inference(resolution,[],[f117,f83])).
% 3.72/0.88  fof(f83,plain,(
% 3.72/0.88    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f5])).
% 3.72/0.88  fof(f5,axiom,(
% 3.72/0.88    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.72/0.88  fof(f117,plain,(
% 3.72/0.88    ( ! [X0] : (~v1_relat_1(k2_zfmisc_1(X0,X0)) | v1_relat_1(k6_partfun1(X0))) )),
% 3.72/0.88    inference(resolution,[],[f76,f99])).
% 3.72/0.88  fof(f76,plain,(
% 3.72/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f34])).
% 3.72/0.88  fof(f34,plain,(
% 3.72/0.88    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f2])).
% 3.72/0.88  fof(f2,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 3.72/0.88  fof(f1356,plain,(
% 3.72/0.88    ~spl4_3 | ~spl4_143 | spl4_141),
% 3.72/0.88    inference(avatar_split_clause,[],[f1346,f1333,f1353,f128])).
% 3.72/0.88  fof(f1333,plain,(
% 3.72/0.88    spl4_141 <=> r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_141])])).
% 3.72/0.88  fof(f1346,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | spl4_141),
% 3.72/0.88    inference(superposition,[],[f1335,f72])).
% 3.72/0.88  fof(f72,plain,(
% 3.72/0.88    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  fof(f30,plain,(
% 3.72/0.88    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(ennf_transformation,[],[f6])).
% 3.72/0.88  fof(f6,axiom,(
% 3.72/0.88    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 3.72/0.88  fof(f1335,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) | spl4_141),
% 3.72/0.88    inference(avatar_component_clause,[],[f1333])).
% 3.72/0.88  fof(f1336,plain,(
% 3.72/0.88    spl4_140 | ~spl4_141 | ~spl4_139),
% 3.72/0.88    inference(avatar_split_clause,[],[f1326,f1320,f1333,f1329])).
% 3.72/0.88  fof(f1320,plain,(
% 3.72/0.88    spl4_139 <=> r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).
% 3.72/0.88  fof(f1326,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(sK2))) | k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) | ~spl4_139),
% 3.72/0.88    inference(resolution,[],[f1322,f89])).
% 3.72/0.88  fof(f1322,plain,(
% 3.72/0.88    r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~spl4_139),
% 3.72/0.88    inference(avatar_component_clause,[],[f1320])).
% 3.72/0.88  fof(f1323,plain,(
% 3.72/0.88    ~spl4_8 | spl4_139 | ~spl4_17 | ~spl4_138),
% 3.72/0.88    inference(avatar_split_clause,[],[f1318,f1314,f397,f1320,f221])).
% 3.72/0.88  fof(f397,plain,(
% 3.72/0.88    spl4_17 <=> v1_relat_1(k4_relat_1(k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 3.72/0.88  fof(f1314,plain,(
% 3.72/0.88    spl4_138 <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 3.72/0.88  fof(f1318,plain,(
% 3.72/0.88    ~v1_relat_1(k4_relat_1(k4_relat_1(sK2))) | r1_tarski(k2_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_138),
% 3.72/0.88    inference(resolution,[],[f1316,f152])).
% 3.72/0.88  fof(f152,plain,(
% 3.72/0.88    ( ! [X2,X3] : (~v4_relat_1(k4_relat_1(X2),X3) | ~v1_relat_1(k4_relat_1(X2)) | r1_tarski(k2_relat_1(X2),X3) | ~v1_relat_1(X2)) )),
% 3.72/0.88    inference(superposition,[],[f86,f71])).
% 3.72/0.88  fof(f71,plain,(
% 3.72/0.88    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f30])).
% 3.72/0.88  fof(f1316,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~spl4_138),
% 3.72/0.88    inference(avatar_component_clause,[],[f1314])).
% 3.72/0.88  fof(f1317,plain,(
% 3.72/0.88    ~spl4_3 | spl4_138 | ~spl4_137),
% 3.72/0.88    inference(avatar_split_clause,[],[f1312,f1305,f1314,f128])).
% 3.72/0.88  fof(f1305,plain,(
% 3.72/0.88    spl4_137 <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 3.72/0.88  fof(f1312,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_137),
% 3.72/0.88    inference(superposition,[],[f1307,f72])).
% 3.72/0.88  fof(f1307,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~spl4_137),
% 3.72/0.88    inference(avatar_component_clause,[],[f1305])).
% 3.72/0.88  fof(f1308,plain,(
% 3.72/0.88    ~spl4_3 | ~spl4_19 | spl4_137 | ~spl4_10 | ~spl4_117),
% 3.72/0.88    inference(avatar_split_clause,[],[f1303,f1182,f230,f1305,f412,f128])).
% 3.72/0.88  fof(f412,plain,(
% 3.72/0.88    spl4_19 <=> v1_relat_1(k6_partfun1(sK1))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 3.72/0.88  fof(f230,plain,(
% 3.72/0.88    spl4_10 <=> sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 3.72/0.88  fof(f1182,plain,(
% 3.72/0.88    spl4_117 <=> v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_117])])).
% 3.72/0.88  fof(f1303,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2) | (~spl4_10 | ~spl4_117)),
% 3.72/0.88    inference(forward_demodulation,[],[f1296,f232])).
% 3.72/0.88  fof(f232,plain,(
% 3.72/0.88    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~spl4_10),
% 3.72/0.88    inference(avatar_component_clause,[],[f230])).
% 3.72/0.88  fof(f1296,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k4_relat_1(k5_relat_1(sK2,k6_partfun1(sK1))))) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2) | ~spl4_117),
% 3.72/0.88    inference(superposition,[],[f1184,f241])).
% 3.72/0.88  fof(f241,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X1,k6_partfun1(X0))) = k5_relat_1(k6_partfun1(X0),k4_relat_1(X1)) | ~v1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 3.72/0.88    inference(superposition,[],[f74,f98])).
% 3.72/0.88  fof(f1184,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))) | ~spl4_117),
% 3.72/0.88    inference(avatar_component_clause,[],[f1182])).
% 3.72/0.88  fof(f1288,plain,(
% 3.72/0.88    ~spl4_134 | spl4_135 | ~spl4_57),
% 3.72/0.88    inference(avatar_split_clause,[],[f1269,f702,f1285,f1281])).
% 3.72/0.88  fof(f702,plain,(
% 3.72/0.88    spl4_57 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 3.72/0.88  fof(f1269,plain,(
% 3.72/0.88    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_57),
% 3.72/0.88    inference(resolution,[],[f532,f704])).
% 3.72/0.88  fof(f704,plain,(
% 3.72/0.88    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_57),
% 3.72/0.88    inference(avatar_component_clause,[],[f702])).
% 3.72/0.88  fof(f532,plain,(
% 3.72/0.88    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 3.72/0.88    inference(resolution,[],[f94,f99])).
% 3.72/0.88  fof(f94,plain,(
% 3.72/0.88    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f47])).
% 3.72/0.88  fof(f47,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.88    inference(flattening,[],[f46])).
% 3.72/0.88  fof(f46,plain,(
% 3.72/0.88    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.72/0.88    inference(ennf_transformation,[],[f19])).
% 3.72/0.88  fof(f19,axiom,(
% 3.72/0.88    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 3.72/0.88  fof(f1216,plain,(
% 3.72/0.88    ~spl4_3 | ~spl4_19 | ~spl4_8 | ~spl4_10 | spl4_112),
% 3.72/0.88    inference(avatar_split_clause,[],[f1215,f1159,f230,f221,f412,f128])).
% 3.72/0.88  fof(f1159,plain,(
% 3.72/0.88    spl4_112 <=> v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_112])])).
% 3.72/0.88  fof(f1215,plain,(
% 3.72/0.88    ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2) | (~spl4_10 | spl4_112)),
% 3.72/0.88    inference(forward_demodulation,[],[f1212,f232])).
% 3.72/0.88  fof(f1212,plain,(
% 3.72/0.88    ~v1_relat_1(k4_relat_1(k5_relat_1(sK2,k6_partfun1(sK1)))) | ~v1_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2) | spl4_112),
% 3.72/0.88    inference(superposition,[],[f1161,f241])).
% 3.72/0.88  fof(f1161,plain,(
% 3.72/0.88    ~v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) | spl4_112),
% 3.72/0.88    inference(avatar_component_clause,[],[f1159])).
% 3.72/0.88  fof(f1185,plain,(
% 3.72/0.88    ~spl4_112 | ~spl4_17 | spl4_117 | ~spl4_108),
% 3.72/0.88    inference(avatar_split_clause,[],[f1151,f1119,f1182,f397,f1159])).
% 3.72/0.88  fof(f1119,plain,(
% 3.72/0.88    spl4_108 <=> k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_108])])).
% 3.72/0.88  fof(f1151,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(k4_relat_1(sK2)),k2_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)))) | ~v1_relat_1(k4_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) | ~spl4_108),
% 3.72/0.88    inference(superposition,[],[f148,f1121])).
% 3.72/0.88  fof(f1121,plain,(
% 3.72/0.88    k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) | ~spl4_108),
% 3.72/0.88    inference(avatar_component_clause,[],[f1119])).
% 3.72/0.88  fof(f148,plain,(
% 3.72/0.88    ( ! [X1] : (v4_relat_1(k4_relat_1(X1),k2_relat_1(X1)) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.72/0.88    inference(superposition,[],[f140,f71])).
% 3.72/0.88  fof(f140,plain,(
% 3.72/0.88    ( ! [X0] : (v4_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(resolution,[],[f85,f106])).
% 3.72/0.88  fof(f106,plain,(
% 3.72/0.88    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.72/0.88    inference(equality_resolution,[],[f88])).
% 3.72/0.88  fof(f88,plain,(
% 3.72/0.88    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.72/0.88    inference(cnf_transformation,[],[f1])).
% 3.72/0.88  fof(f85,plain,(
% 3.72/0.88    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1) | v4_relat_1(X1,X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f43])).
% 3.72/0.88  fof(f1128,plain,(
% 3.72/0.88    ~spl4_19 | ~spl4_8 | spl4_108 | ~spl4_18),
% 3.72/0.88    inference(avatar_split_clause,[],[f1101,f401,f1119,f221,f412])).
% 3.72/0.88  fof(f401,plain,(
% 3.72/0.88    spl4_18 <=> k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 3.72/0.88  fof(f1101,plain,(
% 3.72/0.88    k4_relat_1(k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(k6_partfun1(sK1)) | ~spl4_18),
% 3.72/0.88    inference(superposition,[],[f403,f242])).
% 3.72/0.88  fof(f242,plain,(
% 3.72/0.88    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(k6_partfun1(X0),X1)) = k5_relat_1(k4_relat_1(X1),k6_partfun1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(k6_partfun1(X0))) )),
% 3.72/0.88    inference(superposition,[],[f74,f98])).
% 3.72/0.88  fof(f403,plain,(
% 3.72/0.88    k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1)) | ~spl4_18),
% 3.72/0.88    inference(avatar_component_clause,[],[f401])).
% 3.72/0.88  fof(f725,plain,(
% 3.72/0.88    spl4_56),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f724])).
% 3.72/0.88  fof(f724,plain,(
% 3.72/0.88    $false | spl4_56),
% 3.72/0.88    inference(subsumption_resolution,[],[f52,f700])).
% 3.72/0.88  fof(f700,plain,(
% 3.72/0.88    ~v1_funct_1(sK3) | spl4_56),
% 3.72/0.88    inference(avatar_component_clause,[],[f698])).
% 3.72/0.88  fof(f698,plain,(
% 3.72/0.88    spl4_56 <=> v1_funct_1(sK3)),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 3.72/0.88  fof(f723,plain,(
% 3.72/0.88    spl4_55),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f722])).
% 3.72/0.88  fof(f722,plain,(
% 3.72/0.88    $false | spl4_55),
% 3.72/0.88    inference(subsumption_resolution,[],[f54,f696])).
% 3.72/0.88  fof(f696,plain,(
% 3.72/0.88    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_55),
% 3.72/0.88    inference(avatar_component_clause,[],[f694])).
% 3.72/0.88  fof(f694,plain,(
% 3.72/0.88    spl4_55 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 3.72/0.88  fof(f712,plain,(
% 3.72/0.88    spl4_51),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f711])).
% 3.72/0.88  fof(f711,plain,(
% 3.72/0.88    $false | spl4_51),
% 3.72/0.88    inference(subsumption_resolution,[],[f57,f676])).
% 3.72/0.88  fof(f676,plain,(
% 3.72/0.88    ~v2_funct_1(sK2) | spl4_51),
% 3.72/0.88    inference(avatar_component_clause,[],[f674])).
% 3.72/0.88  fof(f57,plain,(
% 3.72/0.88    v2_funct_1(sK2)),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  fof(f710,plain,(
% 3.72/0.88    ~spl4_3 | spl4_53),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f708])).
% 3.72/0.88  fof(f708,plain,(
% 3.72/0.88    $false | (~spl4_3 | spl4_53)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f130,f61,f684,f77])).
% 3.72/0.88  fof(f77,plain,(
% 3.72/0.88    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.72/0.88    inference(cnf_transformation,[],[f36])).
% 3.72/0.88  fof(f36,plain,(
% 3.72/0.88    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.72/0.88    inference(flattening,[],[f35])).
% 3.72/0.88  fof(f35,plain,(
% 3.72/0.88    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.72/0.88    inference(ennf_transformation,[],[f14])).
% 3.72/0.88  fof(f14,axiom,(
% 3.72/0.88    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 3.72/0.88  fof(f684,plain,(
% 3.72/0.88    ~v1_relat_1(k2_funct_1(sK2)) | spl4_53),
% 3.72/0.88    inference(avatar_component_clause,[],[f682])).
% 3.72/0.88  fof(f130,plain,(
% 3.72/0.88    v1_relat_1(sK2) | ~spl4_3),
% 3.72/0.88    inference(avatar_component_clause,[],[f128])).
% 3.72/0.88  fof(f707,plain,(
% 3.72/0.88    spl4_52),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f706])).
% 3.72/0.88  fof(f706,plain,(
% 3.72/0.88    $false | spl4_52),
% 3.72/0.88    inference(subsumption_resolution,[],[f61,f680])).
% 3.72/0.88  fof(f680,plain,(
% 3.72/0.88    ~v1_funct_1(sK2) | spl4_52),
% 3.72/0.88    inference(avatar_component_clause,[],[f678])).
% 3.72/0.88  fof(f705,plain,(
% 3.72/0.88    ~spl4_52 | ~spl4_55 | ~spl4_56 | ~spl4_5 | spl4_57),
% 3.72/0.88    inference(avatar_split_clause,[],[f690,f702,f202,f698,f694,f678])).
% 3.72/0.88  fof(f202,plain,(
% 3.72/0.88    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 3.72/0.88  fof(f690,plain,(
% 3.72/0.88    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 3.72/0.88    inference(superposition,[],[f56,f95])).
% 3.72/0.88  fof(f56,plain,(
% 3.72/0.88    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  fof(f429,plain,(
% 3.72/0.88    spl4_19),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f424])).
% 3.72/0.88  fof(f424,plain,(
% 3.72/0.88    $false | spl4_19),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f83,f99,f414,f76])).
% 3.72/0.88  fof(f414,plain,(
% 3.72/0.88    ~v1_relat_1(k6_partfun1(sK1)) | spl4_19),
% 3.72/0.88    inference(avatar_component_clause,[],[f412])).
% 3.72/0.88  fof(f408,plain,(
% 3.72/0.88    ~spl4_8 | spl4_17),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f406])).
% 3.72/0.88  fof(f406,plain,(
% 3.72/0.88    $false | (~spl4_8 | spl4_17)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f222,f399,f69])).
% 3.72/0.88  fof(f399,plain,(
% 3.72/0.88    ~v1_relat_1(k4_relat_1(k4_relat_1(sK2))) | spl4_17),
% 3.72/0.88    inference(avatar_component_clause,[],[f397])).
% 3.72/0.88  fof(f222,plain,(
% 3.72/0.88    v1_relat_1(k4_relat_1(sK2)) | ~spl4_8),
% 3.72/0.88    inference(avatar_component_clause,[],[f221])).
% 3.72/0.88  fof(f404,plain,(
% 3.72/0.88    ~spl4_8 | ~spl4_17 | spl4_18 | ~spl4_13),
% 3.72/0.88    inference(avatar_split_clause,[],[f387,f320,f401,f397,f221])).
% 3.72/0.88  fof(f320,plain,(
% 3.72/0.88    spl4_13 <=> sK1 = k1_relat_1(k4_relat_1(sK2))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 3.72/0.88  fof(f387,plain,(
% 3.72/0.88    k4_relat_1(k4_relat_1(sK2)) = k5_relat_1(k4_relat_1(k4_relat_1(sK2)),k6_partfun1(sK1)) | ~v1_relat_1(k4_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~spl4_13),
% 3.72/0.88    inference(superposition,[],[f163,f322])).
% 3.72/0.88  fof(f322,plain,(
% 3.72/0.88    sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_13),
% 3.72/0.88    inference(avatar_component_clause,[],[f320])).
% 3.72/0.88  fof(f163,plain,(
% 3.72/0.88    ( ! [X1] : (k4_relat_1(X1) = k5_relat_1(k4_relat_1(X1),k6_partfun1(k1_relat_1(X1))) | ~v1_relat_1(k4_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.72/0.88    inference(superposition,[],[f102,f72])).
% 3.72/0.88  fof(f332,plain,(
% 3.72/0.88    ~spl4_8 | ~spl4_9 | spl4_14),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f329])).
% 3.72/0.88  fof(f329,plain,(
% 3.72/0.88    $false | (~spl4_8 | ~spl4_9 | spl4_14)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f222,f227,f326,f86])).
% 3.72/0.88  fof(f326,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | spl4_14),
% 3.72/0.88    inference(avatar_component_clause,[],[f324])).
% 3.72/0.88  fof(f324,plain,(
% 3.72/0.88    spl4_14 <=> r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1)),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 3.72/0.88  fof(f227,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(sK2),sK1) | ~spl4_9),
% 3.72/0.88    inference(avatar_component_clause,[],[f225])).
% 3.72/0.88  fof(f225,plain,(
% 3.72/0.88    spl4_9 <=> v4_relat_1(k4_relat_1(sK2),sK1)),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 3.72/0.88  fof(f327,plain,(
% 3.72/0.88    spl4_13 | ~spl4_14 | ~spl4_12),
% 3.72/0.88    inference(avatar_split_clause,[],[f317,f301,f324,f320])).
% 3.72/0.88  fof(f301,plain,(
% 3.72/0.88    spl4_12 <=> r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2)))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 3.72/0.88  fof(f317,plain,(
% 3.72/0.88    ~r1_tarski(k1_relat_1(k4_relat_1(sK2)),sK1) | sK1 = k1_relat_1(k4_relat_1(sK2)) | ~spl4_12),
% 3.72/0.88    inference(resolution,[],[f303,f89])).
% 3.72/0.88  fof(f303,plain,(
% 3.72/0.88    r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | ~spl4_12),
% 3.72/0.88    inference(avatar_component_clause,[],[f301])).
% 3.72/0.88  fof(f304,plain,(
% 3.72/0.88    ~spl4_3 | ~spl4_8 | spl4_12 | ~spl4_6),
% 3.72/0.88    inference(avatar_split_clause,[],[f292,f206,f301,f221,f128])).
% 3.72/0.88  fof(f292,plain,(
% 3.72/0.88    r1_tarski(sK1,k1_relat_1(k4_relat_1(sK2))) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_6),
% 3.72/0.88    inference(superposition,[],[f282,f208])).
% 3.72/0.88  fof(f282,plain,(
% 3.72/0.88    ( ! [X2] : (r1_tarski(k2_relat_1(X2),k1_relat_1(k4_relat_1(X2))) | ~v1_relat_1(k4_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.72/0.88    inference(duplicate_literal_removal,[],[f279])).
% 3.72/0.88  fof(f279,plain,(
% 3.72/0.88    ( ! [X2] : (~v1_relat_1(k4_relat_1(X2)) | r1_tarski(k2_relat_1(X2),k1_relat_1(k4_relat_1(X2))) | ~v1_relat_1(X2) | ~v1_relat_1(k4_relat_1(X2))) )),
% 3.72/0.88    inference(resolution,[],[f152,f140])).
% 3.72/0.88  fof(f236,plain,(
% 3.72/0.88    ~spl4_3 | spl4_8),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f234])).
% 3.72/0.88  fof(f234,plain,(
% 3.72/0.88    $false | (~spl4_3 | spl4_8)),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f130,f223,f69])).
% 3.72/0.88  fof(f223,plain,(
% 3.72/0.88    ~v1_relat_1(k4_relat_1(sK2)) | spl4_8),
% 3.72/0.88    inference(avatar_component_clause,[],[f221])).
% 3.72/0.88  fof(f233,plain,(
% 3.72/0.88    ~spl4_3 | spl4_10 | ~spl4_6),
% 3.72/0.88    inference(avatar_split_clause,[],[f215,f206,f230,f128])).
% 3.72/0.88  fof(f215,plain,(
% 3.72/0.88    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) | ~v1_relat_1(sK2) | ~spl4_6),
% 3.72/0.88    inference(superposition,[],[f102,f208])).
% 3.72/0.88  fof(f228,plain,(
% 3.72/0.88    ~spl4_3 | ~spl4_8 | spl4_9 | ~spl4_6),
% 3.72/0.88    inference(avatar_split_clause,[],[f214,f206,f225,f221,f128])).
% 3.72/0.88  fof(f214,plain,(
% 3.72/0.88    v4_relat_1(k4_relat_1(sK2),sK1) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_6),
% 3.72/0.88    inference(superposition,[],[f148,f208])).
% 3.72/0.88  fof(f212,plain,(
% 3.72/0.88    spl4_5),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f211])).
% 3.72/0.88  fof(f211,plain,(
% 3.72/0.88    $false | spl4_5),
% 3.72/0.88    inference(subsumption_resolution,[],[f63,f204])).
% 3.72/0.88  fof(f204,plain,(
% 3.72/0.88    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 3.72/0.88    inference(avatar_component_clause,[],[f202])).
% 3.72/0.88  fof(f210,plain,(
% 3.72/0.88    ~spl4_5 | spl4_6),
% 3.72/0.88    inference(avatar_split_clause,[],[f200,f206,f202])).
% 3.72/0.88  fof(f200,plain,(
% 3.72/0.88    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.72/0.88    inference(superposition,[],[f55,f90])).
% 3.72/0.88  fof(f90,plain,(
% 3.72/0.88    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.72/0.88    inference(cnf_transformation,[],[f44])).
% 3.72/0.88  fof(f44,plain,(
% 3.72/0.88    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.72/0.88    inference(ennf_transformation,[],[f18])).
% 3.72/0.88  fof(f18,axiom,(
% 3.72/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.72/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 3.72/0.88  fof(f55,plain,(
% 3.72/0.88    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 3.72/0.88    inference(cnf_transformation,[],[f27])).
% 3.72/0.88  fof(f146,plain,(
% 3.72/0.88    spl4_4),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f143])).
% 3.72/0.88  fof(f143,plain,(
% 3.72/0.88    $false | spl4_4),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f83,f134])).
% 3.72/0.88  fof(f134,plain,(
% 3.72/0.88    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 3.72/0.88    inference(avatar_component_clause,[],[f132])).
% 3.72/0.88  fof(f132,plain,(
% 3.72/0.88    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 3.72/0.88  fof(f139,plain,(
% 3.72/0.88    spl4_2),
% 3.72/0.88    inference(avatar_contradiction_clause,[],[f136])).
% 3.72/0.88  fof(f136,plain,(
% 3.72/0.88    $false | spl4_2),
% 3.72/0.88    inference(unit_resulting_resolution,[],[f83,f125])).
% 3.72/0.88  fof(f125,plain,(
% 3.72/0.88    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 3.72/0.88    inference(avatar_component_clause,[],[f123])).
% 3.72/0.88  fof(f123,plain,(
% 3.72/0.88    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 3.72/0.88    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 3.72/0.88  fof(f135,plain,(
% 3.72/0.88    spl4_3 | ~spl4_4),
% 3.72/0.88    inference(avatar_split_clause,[],[f116,f132,f128])).
% 3.72/0.88  fof(f116,plain,(
% 3.72/0.88    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 3.72/0.88    inference(resolution,[],[f76,f63])).
% 3.72/0.88  fof(f126,plain,(
% 3.72/0.88    spl4_1 | ~spl4_2),
% 3.72/0.88    inference(avatar_split_clause,[],[f115,f123,f119])).
% 3.72/0.88  fof(f115,plain,(
% 3.72/0.88    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 3.72/0.88    inference(resolution,[],[f76,f54])).
% 3.72/0.88  % SZS output end Proof for theBenchmark
% 3.72/0.88  % (14942)------------------------------
% 3.72/0.88  % (14942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.72/0.88  % (14942)Termination reason: Refutation
% 3.72/0.88  
% 3.72/0.88  % (14942)Memory used [KB]: 9594
% 3.72/0.88  % (14942)Time elapsed: 0.454 s
% 3.72/0.88  % (14942)------------------------------
% 3.72/0.88  % (14942)------------------------------
% 3.72/0.88  % (14928)Success in time 0.512 s
%------------------------------------------------------------------------------
