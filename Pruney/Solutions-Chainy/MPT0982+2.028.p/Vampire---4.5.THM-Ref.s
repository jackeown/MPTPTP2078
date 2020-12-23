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
% DateTime   : Thu Dec  3 13:01:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 285 expanded)
%              Number of leaves         :   38 ( 113 expanded)
%              Depth                    :   10
%              Number of atoms          :  454 ( 999 expanded)
%              Number of equality atoms :  112 ( 250 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f998,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f98,f102,f106,f130,f153,f157,f162,f174,f208,f213,f218,f222,f231,f430,f580,f591,f670,f996,f997])).

fof(f997,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) != k2_relat_1(k5_relat_1(sK3,sK4))
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4)
    | k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != k2_relat_1(k5_relat_1(sK3,sK4))
    | sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | sK1 != k10_relat_1(sK4,sK2)
    | k2_relat_1(sK3) != k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3)))
    | sK1 = k2_relat_1(sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f996,plain,
    ( spl5_114
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f471,f428,f994])).

fof(f994,plain,
    ( spl5_114
  <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).

fof(f428,plain,
    ( spl5_52
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f471,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_52 ),
    inference(resolution,[],[f429,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f429,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f428])).

fof(f670,plain,
    ( spl5_87
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f531,f151,f128,f668])).

fof(f668,plain,
    ( spl5_87
  <=> k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f128,plain,
    ( spl5_10
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f151,plain,
    ( spl5_11
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f531,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f158,f129])).

fof(f129,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f128])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3)) )
    | ~ spl5_11 ),
    inference(resolution,[],[f152,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

fof(f152,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f591,plain,
    ( spl5_70
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f372,f220,f160,f128,f76,f72,f589])).

fof(f589,plain,
    ( spl5_70
  <=> k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f72,plain,
    ( spl5_1
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f76,plain,
    ( spl5_2
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f160,plain,
    ( spl5_13
  <=> sK1 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f220,plain,
    ( spl5_26
  <=> r1_tarski(k2_relat_1(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f372,plain,
    ( k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_13
    | ~ spl5_26 ),
    inference(resolution,[],[f166,f221])).

fof(f221,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f220])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f165,f77])).

fof(f77,plain,
    ( v2_funct_1(sK4)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v2_funct_1(sK4)
        | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f164,f129])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_relat_1(sK4)
        | ~ v2_funct_1(sK4)
        | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f163,f73])).

fof(f73,plain,
    ( v1_funct_1(sK4)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | ~ v1_funct_1(sK4)
        | ~ v1_relat_1(sK4)
        | ~ v2_funct_1(sK4)
        | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 )
    | ~ spl5_13 ),
    inference(superposition,[],[f53,f161])).

fof(f161,plain,
    ( sK1 = k1_relat_1(sK4)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f160])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f580,plain,
    ( spl5_67
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f421,f104,f96,f80,f72,f578])).

fof(f578,plain,
    ( spl5_67
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f80,plain,
    ( spl5_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f96,plain,
    ( spl5_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f104,plain,
    ( spl5_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f421,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_1
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f418,f73])).

fof(f418,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_3
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f146,f97])).

fof(f97,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f146,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | ~ v1_funct_1(X0)
        | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0) )
    | ~ spl5_3
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f136,f81])).

fof(f81,plain,
    ( v1_funct_1(sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f136,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0) )
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
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
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f430,plain,
    ( spl5_52
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f383,f104,f96,f428])).

fof(f383,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(forward_demodulation,[],[f381,f316])).

fof(f316,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f140,f97])).

fof(f140,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
        | k4_relset_1(sK0,sK1,X5,X6,sK3,X4) = k5_relat_1(sK3,X4) )
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f381,plain,
    ( m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl5_7
    | ~ spl5_9 ),
    inference(resolution,[],[f143,f97])).

fof(f143,plain,
    ( ! [X8,X7,X9] :
        ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | m1_subset_1(k4_relset_1(sK0,sK1,X8,X9,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(sK0,X9))) )
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f231,plain,
    ( ~ spl5_28
    | spl5_8
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f227,f216,f100,f229])).

fof(f229,plain,
    ( spl5_28
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f100,plain,
    ( spl5_8
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f216,plain,
    ( spl5_25
  <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f227,plain,
    ( sK1 != k2_relat_1(sK3)
    | spl5_8
    | ~ spl5_25 ),
    inference(superposition,[],[f101,f217])).

fof(f217,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f216])).

fof(f101,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f222,plain,
    ( spl5_26
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f214,f211,f220])).

fof(f211,plain,
    ( spl5_24
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f214,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1)
    | ~ spl5_24 ),
    inference(resolution,[],[f212,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f212,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f211])).

fof(f218,plain,
    ( spl5_25
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f135,f104,f216])).

fof(f135,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f55])).

fof(f213,plain,
    ( spl5_24
    | ~ spl5_9
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f209,f206,f104,f211])).

fof(f206,plain,
    ( spl5_23
  <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f209,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl5_9
    | ~ spl5_23 ),
    inference(forward_demodulation,[],[f207,f135])).

fof(f207,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f206])).

fof(f208,plain,
    ( spl5_23
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f134,f104,f206])).

fof(f134,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f174,plain,
    ( spl5_15
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f126,f96,f88,f84,f172])).

fof(f172,plain,
    ( spl5_15
  <=> sK1 = k10_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f84,plain,
    ( spl5_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f88,plain,
    ( spl5_5
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f126,plain,
    ( sK1 = k10_relat_1(sK4,sK2)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f125,f121])).

fof(f121,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f120,f89])).

fof(f89,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f120,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | spl5_4
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f108,f85])).

fof(f85,plain,
    ( k1_xboole_0 != sK2
    | spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f108,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f125,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2)
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f117,f113])).

fof(f113,plain,
    ( ! [X3] : k8_relset_1(sK1,sK2,sK4,X3) = k10_relat_1(sK4,X3)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f117,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,sK2)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f162,plain,
    ( spl5_13
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f123,f96,f88,f84,f160])).

fof(f123,plain,
    ( sK1 = k1_relat_1(sK4)
    | spl5_4
    | ~ spl5_5
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f112,f121])).

fof(f112,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f157,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f40,f155])).

fof(f155,plain,
    ( spl5_12
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f40,plain,(
    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

fof(f153,plain,
    ( spl5_11
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f139,f104,f151])).

fof(f139,plain,
    ( v1_relat_1(sK3)
    | ~ spl5_9 ),
    inference(resolution,[],[f105,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f130,plain,
    ( spl5_10
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f114,f96,f128])).

fof(f114,plain,
    ( v1_relat_1(sK4)
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f61])).

fof(f106,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f46,f104])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f43,f100])).

fof(f43,plain,(
    sK1 != k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f98,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f39,f96])).

fof(f39,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f88])).

fof(f38,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f18])).

fof(f82,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f44,f80])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f78,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).

fof(f74,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:01:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (10150)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.42  % (10166)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.44  % (10150)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f998,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f98,f102,f106,f130,f153,f157,f162,f174,f208,f213,f218,f222,f231,f430,f580,f591,f670,f996,f997])).
% 0.21/0.44  fof(f997,plain,(
% 0.21/0.44    k9_relat_1(sK4,k2_relat_1(sK3)) != k2_relat_1(k5_relat_1(sK3,sK4)) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) != k5_relat_1(sK3,sK4) | k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) != k2_relat_1(k5_relat_1(sK3,sK4)) | sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) | sK1 != k10_relat_1(sK4,sK2) | k2_relat_1(sK3) != k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) | sK1 = k2_relat_1(sK3)),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f996,plain,(
% 0.21/0.44    spl5_114 | ~spl5_52),
% 0.21/0.44    inference(avatar_split_clause,[],[f471,f428,f994])).
% 0.21/0.44  fof(f994,plain,(
% 0.21/0.44    spl5_114 <=> k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_114])])).
% 0.21/0.44  fof(f428,plain,(
% 0.21/0.44    spl5_52 <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.44  fof(f471,plain,(
% 0.21/0.44    k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) | ~spl5_52),
% 0.21/0.44    inference(resolution,[],[f429,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.44  fof(f429,plain,(
% 0.21/0.44    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~spl5_52),
% 0.21/0.44    inference(avatar_component_clause,[],[f428])).
% 0.21/0.44  fof(f670,plain,(
% 0.21/0.44    spl5_87 | ~spl5_10 | ~spl5_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f531,f151,f128,f668])).
% 0.21/0.44  fof(f668,plain,(
% 0.21/0.44    spl5_87 <=> k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    spl5_10 <=> v1_relat_1(sK4)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl5_11 <=> v1_relat_1(sK3)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.44  fof(f531,plain,(
% 0.21/0.44    k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) | (~spl5_10 | ~spl5_11)),
% 0.21/0.44    inference(resolution,[],[f158,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    v1_relat_1(sK4) | ~spl5_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f128])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(k5_relat_1(sK3,X0)) = k9_relat_1(X0,k2_relat_1(sK3))) ) | ~spl5_11),
% 0.21/0.44    inference(resolution,[],[f152,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).
% 0.21/0.45  fof(f152,plain,(
% 0.21/0.45    v1_relat_1(sK3) | ~spl5_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f151])).
% 0.21/0.45  fof(f591,plain,(
% 0.21/0.45    spl5_70 | ~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_13 | ~spl5_26),
% 0.21/0.45    inference(avatar_split_clause,[],[f372,f220,f160,f128,f76,f72,f589])).
% 0.21/0.45  fof(f589,plain,(
% 0.21/0.45    spl5_70 <=> k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    spl5_1 <=> v1_funct_1(sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    spl5_2 <=> v2_funct_1(sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.45  fof(f160,plain,(
% 0.21/0.45    spl5_13 <=> sK1 = k1_relat_1(sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.45  fof(f220,plain,(
% 0.21/0.45    spl5_26 <=> r1_tarski(k2_relat_1(sK3),sK1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.45  fof(f372,plain,(
% 0.21/0.45    k2_relat_1(sK3) = k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_13 | ~spl5_26)),
% 0.21/0.45    inference(resolution,[],[f166,f221])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_26),
% 0.21/0.45    inference(avatar_component_clause,[],[f220])).
% 0.21/0.45  fof(f166,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) ) | (~spl5_1 | ~spl5_2 | ~spl5_10 | ~spl5_13)),
% 0.21/0.45    inference(subsumption_resolution,[],[f165,f77])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    v2_funct_1(sK4) | ~spl5_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f76])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v2_funct_1(sK4) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) ) | (~spl5_1 | ~spl5_10 | ~spl5_13)),
% 0.21/0.45    inference(subsumption_resolution,[],[f164,f129])).
% 0.21/0.45  fof(f164,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v1_relat_1(sK4) | ~v2_funct_1(sK4) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) ) | (~spl5_1 | ~spl5_13)),
% 0.21/0.45    inference(subsumption_resolution,[],[f163,f73])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    v1_funct_1(sK4) | ~spl5_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f72])).
% 0.21/0.45  fof(f163,plain,(
% 0.21/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | ~v2_funct_1(sK4) | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0) ) | ~spl5_13),
% 0.21/0.45    inference(superposition,[],[f53,f161])).
% 0.21/0.45  fof(f161,plain,(
% 0.21/0.45    sK1 = k1_relat_1(sK4) | ~spl5_13),
% 0.21/0.45    inference(avatar_component_clause,[],[f160])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.45  fof(f580,plain,(
% 0.21/0.45    spl5_67 | ~spl5_1 | ~spl5_3 | ~spl5_7 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f421,f104,f96,f80,f72,f578])).
% 0.21/0.45  fof(f578,plain,(
% 0.21/0.45    spl5_67 <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl5_3 <=> v1_funct_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    spl5_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl5_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.45  fof(f421,plain,(
% 0.21/0.45    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_1 | ~spl5_3 | ~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(subsumption_resolution,[],[f418,f73])).
% 0.21/0.45  fof(f418,plain,(
% 0.21/0.45    ~v1_funct_1(sK4) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_3 | ~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(resolution,[],[f146,f97])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~spl5_7),
% 0.21/0.45    inference(avatar_component_clause,[],[f96])).
% 0.21/0.45  fof(f146,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0)) ) | (~spl5_3 | ~spl5_9)),
% 0.21/0.45    inference(subsumption_resolution,[],[f136,f81])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    v1_funct_1(sK3) | ~spl5_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f80])).
% 0.21/0.45  fof(f136,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k5_relat_1(sK3,X0) = k1_partfun1(sK0,sK1,X1,X2,sK3,X0)) ) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.45    inference(flattening,[],[f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.45    inference(ennf_transformation,[],[f13])).
% 0.21/0.45  fof(f13,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.45  fof(f105,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f104])).
% 0.21/0.45  fof(f430,plain,(
% 0.21/0.45    spl5_52 | ~spl5_7 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f383,f104,f96,f428])).
% 0.21/0.45  fof(f383,plain,(
% 0.21/0.45    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(forward_demodulation,[],[f381,f316])).
% 0.21/0.45  fof(f316,plain,(
% 0.21/0.45    k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) | (~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(resolution,[],[f140,f97])).
% 0.21/0.45  fof(f140,plain,(
% 0.21/0.45    ( ! [X6,X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) | k4_relset_1(sK0,sK1,X5,X6,sK3,X4) = k5_relat_1(sK3,X4)) ) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f62])).
% 0.21/0.45  fof(f62,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.45    inference(ennf_transformation,[],[f9])).
% 0.21/0.45  fof(f9,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 0.21/0.45  fof(f381,plain,(
% 0.21/0.45    m1_subset_1(k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | (~spl5_7 | ~spl5_9)),
% 0.21/0.45    inference(resolution,[],[f143,f97])).
% 0.21/0.45  fof(f143,plain,(
% 0.21/0.45    ( ! [X8,X7,X9] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | m1_subset_1(k4_relset_1(sK0,sK1,X8,X9,sK3,X7),k1_zfmisc_1(k2_zfmisc_1(sK0,X9)))) ) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f65])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    ~spl5_28 | spl5_8 | ~spl5_25),
% 0.21/0.45    inference(avatar_split_clause,[],[f227,f216,f100,f229])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    spl5_28 <=> sK1 = k2_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.45  fof(f100,plain,(
% 0.21/0.45    spl5_8 <=> sK1 = k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.45  fof(f216,plain,(
% 0.21/0.45    spl5_25 <=> k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    sK1 != k2_relat_1(sK3) | (spl5_8 | ~spl5_25)),
% 0.21/0.45    inference(superposition,[],[f101,f217])).
% 0.21/0.45  fof(f217,plain,(
% 0.21/0.45    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl5_25),
% 0.21/0.45    inference(avatar_component_clause,[],[f216])).
% 0.21/0.45  fof(f101,plain,(
% 0.21/0.45    sK1 != k2_relset_1(sK0,sK1,sK3) | spl5_8),
% 0.21/0.45    inference(avatar_component_clause,[],[f100])).
% 0.21/0.45  fof(f222,plain,(
% 0.21/0.45    spl5_26 | ~spl5_24),
% 0.21/0.45    inference(avatar_split_clause,[],[f214,f211,f220])).
% 0.21/0.45  fof(f211,plain,(
% 0.21/0.45    spl5_24 <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.45  fof(f214,plain,(
% 0.21/0.45    r1_tarski(k2_relat_1(sK3),sK1) | ~spl5_24),
% 0.21/0.45    inference(resolution,[],[f212,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.45    inference(ennf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.45    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.45  fof(f212,plain,(
% 0.21/0.45    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | ~spl5_24),
% 0.21/0.45    inference(avatar_component_clause,[],[f211])).
% 0.21/0.45  fof(f218,plain,(
% 0.21/0.45    spl5_25 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f135,f104,f216])).
% 0.21/0.45  fof(f135,plain,(
% 0.21/0.45    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f55])).
% 0.21/0.45  fof(f213,plain,(
% 0.21/0.45    spl5_24 | ~spl5_9 | ~spl5_23),
% 0.21/0.45    inference(avatar_split_clause,[],[f209,f206,f104,f211])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    spl5_23 <=> m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.45  fof(f209,plain,(
% 0.21/0.45    m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) | (~spl5_9 | ~spl5_23)),
% 0.21/0.45    inference(forward_demodulation,[],[f207,f135])).
% 0.21/0.45  fof(f207,plain,(
% 0.21/0.45    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl5_23),
% 0.21/0.45    inference(avatar_component_clause,[],[f206])).
% 0.21/0.45  fof(f208,plain,(
% 0.21/0.45    spl5_23 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f134,f104,f206])).
% 0.21/0.45  fof(f134,plain,(
% 0.21/0.45    m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))) )),
% 0.21/0.45    inference(cnf_transformation,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 0.21/0.45  fof(f174,plain,(
% 0.21/0.45    spl5_15 | spl5_4 | ~spl5_5 | ~spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f126,f96,f88,f84,f172])).
% 0.21/0.45  fof(f172,plain,(
% 0.21/0.45    spl5_15 <=> sK1 = k10_relat_1(sK4,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    spl5_4 <=> k1_xboole_0 = sK2),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.45  fof(f88,plain,(
% 0.21/0.45    spl5_5 <=> v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.45  fof(f126,plain,(
% 0.21/0.45    sK1 = k10_relat_1(sK4,sK2) | (spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f125,f121])).
% 0.21/0.45  fof(f121,plain,(
% 0.21/0.45    sK1 = k1_relset_1(sK1,sK2,sK4) | (spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.45    inference(subsumption_resolution,[],[f120,f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    v1_funct_2(sK4,sK1,sK2) | ~spl5_5),
% 0.21/0.45    inference(avatar_component_clause,[],[f88])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2) | (spl5_4 | ~spl5_7)),
% 0.21/0.45    inference(subsumption_resolution,[],[f108,f85])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    k1_xboole_0 != sK2 | spl5_4),
% 0.21/0.45    inference(avatar_component_clause,[],[f84])).
% 0.21/0.45  fof(f108,plain,(
% 0.21/0.45    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~v1_funct_2(sK4,sK1,sK2) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f97,f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.45  fof(f125,plain,(
% 0.21/0.45    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2) | ~spl5_7),
% 0.21/0.45    inference(forward_demodulation,[],[f117,f113])).
% 0.21/0.45  fof(f113,plain,(
% 0.21/0.45    ( ! [X3] : (k8_relset_1(sK1,sK2,sK4,X3) = k10_relat_1(sK4,X3)) ) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f97,f58])).
% 0.21/0.45  fof(f58,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,axiom,(
% 0.21/0.45    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,sK2) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f97,f64])).
% 0.21/0.45  fof(f64,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.45  fof(f162,plain,(
% 0.21/0.45    spl5_13 | spl5_4 | ~spl5_5 | ~spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f123,f96,f88,f84,f160])).
% 0.21/0.45  fof(f123,plain,(
% 0.21/0.45    sK1 = k1_relat_1(sK4) | (spl5_4 | ~spl5_5 | ~spl5_7)),
% 0.21/0.45    inference(forward_demodulation,[],[f112,f121])).
% 0.21/0.45  fof(f112,plain,(
% 0.21/0.45    k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f97,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f27])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f7])).
% 0.21/0.45  fof(f7,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.45  fof(f157,plain,(
% 0.21/0.45    spl5_12),
% 0.21/0.45    inference(avatar_split_clause,[],[f40,f155])).
% 0.21/0.45  fof(f155,plain,(
% 0.21/0.45    spl5_12 <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.45    inference(ennf_transformation,[],[f15])).
% 0.21/0.45  fof(f15,negated_conjecture,(
% 0.21/0.45    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.45    inference(negated_conjecture,[],[f14])).
% 0.21/0.45  fof(f14,conjecture,(
% 0.21/0.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).
% 0.21/0.45  fof(f153,plain,(
% 0.21/0.45    spl5_11 | ~spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f139,f104,f151])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    v1_relat_1(sK3) | ~spl5_9),
% 0.21/0.45    inference(resolution,[],[f105,f61])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f31])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.45  fof(f130,plain,(
% 0.21/0.45    spl5_10 | ~spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f114,f96,f128])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    v1_relat_1(sK4) | ~spl5_7),
% 0.21/0.45    inference(resolution,[],[f97,f61])).
% 0.21/0.45  fof(f106,plain,(
% 0.21/0.45    spl5_9),
% 0.21/0.45    inference(avatar_split_clause,[],[f46,f104])).
% 0.21/0.45  fof(f46,plain,(
% 0.21/0.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    ~spl5_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f43,f100])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    sK1 != k2_relset_1(sK0,sK1,sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    spl5_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f39,f96])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl5_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f38,f88])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    v1_funct_2(sK4,sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f86,plain,(
% 0.21/0.45    ~spl5_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f42,f84])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    k1_xboole_0 != sK2),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl5_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f44,f80])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    v1_funct_1(sK3)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    spl5_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f41,f76])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    v2_funct_1(sK4)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    spl5_1),
% 0.21/0.45    inference(avatar_split_clause,[],[f37,f72])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    v1_funct_1(sK4)),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (10150)------------------------------
% 0.21/0.45  % (10150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (10150)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (10150)Memory used [KB]: 7164
% 0.21/0.45  % (10150)Time elapsed: 0.050 s
% 0.21/0.45  % (10150)------------------------------
% 0.21/0.45  % (10150)------------------------------
% 0.21/0.45  % (10149)Success in time 0.097 s
%------------------------------------------------------------------------------
