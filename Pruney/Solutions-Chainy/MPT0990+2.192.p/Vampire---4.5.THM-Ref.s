%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:02 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  226 ( 478 expanded)
%              Number of leaves         :   51 ( 179 expanded)
%              Depth                    :    8
%              Number of atoms          :  791 (2259 expanded)
%              Number of equality atoms :  169 ( 658 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f797,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f106,f110,f114,f129,f131,f149,f180,f182,f184,f230,f237,f263,f289,f291,f293,f302,f350,f418,f431,f443,f536,f551,f623,f631,f655,f667,f697,f719,f722,f735,f741,f760,f764,f769,f794])).

fof(f794,plain,
    ( ~ spl4_20
    | ~ spl4_74 ),
    inference(avatar_contradiction_clause,[],[f787])).

fof(f787,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_74 ),
    inference(subsumption_resolution,[],[f46,f771])).

fof(f771,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_20
    | ~ spl4_74 ),
    inference(forward_demodulation,[],[f680,f250])).

fof(f250,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_20
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f680,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_74 ),
    inference(avatar_component_clause,[],[f678])).

fof(f678,plain,
    ( spl4_74
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f769,plain,
    ( ~ spl4_20
    | ~ spl4_28
    | spl4_78 ),
    inference(avatar_contradiction_clause,[],[f768])).

fof(f768,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_28
    | spl4_78 ),
    inference(subsumption_resolution,[],[f360,f766])).

fof(f766,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_20
    | spl4_78 ),
    inference(forward_demodulation,[],[f696,f250])).

fof(f696,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_78 ),
    inference(avatar_component_clause,[],[f694])).

fof(f694,plain,
    ( spl4_78
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).

fof(f360,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_28 ),
    inference(forward_demodulation,[],[f355,f77])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f56,f50])).

fof(f50,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f56,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f355,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_28 ),
    inference(superposition,[],[f77,f300])).

fof(f300,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl4_28
  <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f764,plain,
    ( ~ spl4_6
    | ~ spl4_20
    | spl4_77 ),
    inference(avatar_contradiction_clause,[],[f763])).

fof(f763,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_20
    | spl4_77 ),
    inference(trivial_inequality_removal,[],[f762])).

fof(f762,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_6
    | ~ spl4_20
    | spl4_77 ),
    inference(forward_demodulation,[],[f761,f127])).

fof(f127,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_6
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f761,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_20
    | spl4_77 ),
    inference(forward_demodulation,[],[f692,f250])).

fof(f692,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_77 ),
    inference(avatar_component_clause,[],[f690])).

fof(f690,plain,
    ( spl4_77
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).

fof(f760,plain,
    ( ~ spl4_20
    | spl4_76 ),
    inference(avatar_contradiction_clause,[],[f759])).

fof(f759,plain,
    ( $false
    | ~ spl4_20
    | spl4_76 ),
    inference(subsumption_resolution,[],[f43,f743])).

fof(f743,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_20
    | spl4_76 ),
    inference(forward_demodulation,[],[f688,f250])).

fof(f688,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_76 ),
    inference(avatar_component_clause,[],[f686])).

fof(f686,plain,
    ( spl4_76
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f741,plain,
    ( ~ spl4_20
    | spl4_75 ),
    inference(avatar_contradiction_clause,[],[f740])).

fof(f740,plain,
    ( $false
    | ~ spl4_20
    | spl4_75 ),
    inference(unit_resulting_resolution,[],[f61,f49,f736,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f736,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl4_20
    | spl4_75 ),
    inference(forward_demodulation,[],[f684,f250])).

fof(f684,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_75 ),
    inference(avatar_component_clause,[],[f682])).

fof(f682,plain,
    ( spl4_75
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f735,plain,
    ( ~ spl4_20
    | spl4_72 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | ~ spl4_20
    | spl4_72 ),
    inference(subsumption_resolution,[],[f47,f723])).

fof(f723,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_20
    | spl4_72 ),
    inference(superposition,[],[f671,f250])).

fof(f671,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_72 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl4_72
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f722,plain,
    ( spl4_22
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f721])).

fof(f721,plain,
    ( $false
    | spl4_22
    | ~ spl4_42 ),
    inference(trivial_inequality_removal,[],[f720])).

fof(f720,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_22
    | ~ spl4_42 ),
    inference(forward_demodulation,[],[f258,f441])).

fof(f441,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f439])).

fof(f439,plain,
    ( spl4_42
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f258,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f719,plain,
    ( spl4_23
    | ~ spl4_71 ),
    inference(avatar_contradiction_clause,[],[f718])).

fof(f718,plain,
    ( $false
    | spl4_23
    | ~ spl4_71 ),
    inference(subsumption_resolution,[],[f262,f716])).

fof(f716,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_71 ),
    inference(forward_demodulation,[],[f706,f77])).

fof(f706,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1))
    | ~ spl4_71 ),
    inference(superposition,[],[f77,f665])).

fof(f665,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_71 ),
    inference(avatar_component_clause,[],[f663])).

fof(f663,plain,
    ( spl4_71
  <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).

fof(f262,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f697,plain,
    ( spl4_74
    | ~ spl4_75
    | ~ spl4_76
    | ~ spl4_11
    | ~ spl4_1
    | ~ spl4_72
    | ~ spl4_77
    | ~ spl4_78
    | ~ spl4_42
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f676,f529,f439,f694,f690,f669,f90,f166,f686,f682,f678])).

fof(f166,plain,
    ( spl4_11
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f90,plain,
    ( spl4_1
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f529,plain,
    ( spl4_56
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f676,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_42
    | ~ spl4_56 ),
    inference(forward_demodulation,[],[f661,f441])).

fof(f661,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_56 ),
    inference(superposition,[],[f81,f531])).

fof(f531,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_56 ),
    inference(avatar_component_clause,[],[f529])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f60,f50])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
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
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f667,plain,
    ( ~ spl4_1
    | ~ spl4_21
    | ~ spl4_11
    | spl4_71
    | ~ spl4_56 ),
    inference(avatar_split_clause,[],[f659,f529,f663,f166,f252,f90])).

fof(f252,plain,
    ( spl4_21
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f659,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_56 ),
    inference(superposition,[],[f80,f531])).

fof(f80,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f58,f50])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f655,plain,(
    ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f632])).

fof(f632,plain,
    ( $false
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f44,f535])).

fof(f535,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f533])).

fof(f533,plain,
    ( spl4_57
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f631,plain,(
    spl4_69 ),
    inference(avatar_contradiction_clause,[],[f628])).

fof(f628,plain,
    ( $false
    | spl4_69 ),
    inference(unit_resulting_resolution,[],[f75,f622])).

fof(f622,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_69 ),
    inference(avatar_component_clause,[],[f620])).

fof(f620,plain,
    ( spl4_69
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).

fof(f75,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f52,f50])).

fof(f52,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f623,plain,
    ( ~ spl4_40
    | ~ spl4_10
    | ~ spl4_11
    | spl4_57
    | spl4_21
    | ~ spl4_69
    | ~ spl4_8
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f616,f549,f146,f620,f252,f533,f166,f162,f415])).

fof(f415,plain,
    ( spl4_40
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f162,plain,
    ( spl4_10
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f146,plain,
    ( spl4_8
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f549,plain,
    ( spl4_59
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f616,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8
    | ~ spl4_59 ),
    inference(superposition,[],[f550,f148])).

fof(f148,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f146])).

fof(f550,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f549])).

fof(f551,plain,
    ( ~ spl4_9
    | spl4_59
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f547,f286,f121,f549,f158])).

fof(f158,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f121,plain,
    ( spl4_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f286,plain,
    ( spl4_27
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f547,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(trivial_inequality_removal,[],[f542])).

fof(f542,plain,(
    ! [X0,X1] :
      ( sK1 != sK1
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK1,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
      | ~ v1_funct_1(sK2)
      | k1_xboole_0 = X1
      | v2_funct_1(X0) ) ),
    inference(superposition,[],[f69,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ v1_funct_1(X3)
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f536,plain,
    ( spl4_56
    | spl4_57
    | ~ spl4_21
    | ~ spl4_11
    | ~ spl4_10
    | ~ spl4_40
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f436,f411,f415,f162,f166,f252,f533,f529])).

fof(f411,plain,
    ( spl4_39
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f436,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_39 ),
    inference(trivial_inequality_removal,[],[f434])).

fof(f434,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_39 ),
    inference(superposition,[],[f63,f413])).

fof(f413,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_39 ),
    inference(avatar_component_clause,[],[f411])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f443,plain,
    ( ~ spl4_10
    | spl4_42
    | ~ spl4_39 ),
    inference(avatar_split_clause,[],[f435,f411,f439,f162])).

fof(f435,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_39 ),
    inference(superposition,[],[f62,f413])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f431,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f430])).

fof(f430,plain,
    ( $false
    | spl4_40 ),
    inference(subsumption_resolution,[],[f39,f417])).

fof(f417,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f415])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f418,plain,
    ( spl4_39
    | ~ spl4_11
    | ~ spl4_5
    | ~ spl4_27
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_40 ),
    inference(avatar_split_clause,[],[f405,f415,f162,f158,f286,f121,f166,f411])).

fof(f405,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f65,f42])).

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f350,plain,(
    ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f45,f280])).

fof(f280,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f19])).

fof(f302,plain,
    ( ~ spl4_3
    | ~ spl4_26
    | ~ spl4_9
    | spl4_28
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f295,f274,f298,f158,f282,f99])).

fof(f99,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f282,plain,
    ( spl4_26
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f274,plain,
    ( spl4_24
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f295,plain,
    ( k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f80,f276])).

fof(f276,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f274])).

fof(f293,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f292])).

fof(f292,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f48,f288])).

fof(f288,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f286])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f291,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f290])).

fof(f290,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f43,f284])).

fof(f284,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f282])).

fof(f289,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_26
    | ~ spl4_9
    | ~ spl4_5
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f272,f286,f121,f158,f282,f278,f274])).

fof(f272,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f63,f41])).

fof(f263,plain,
    ( spl4_20
    | ~ spl4_1
    | ~ spl4_21
    | ~ spl4_9
    | ~ spl4_3
    | ~ spl4_11
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f246,f191,f125,f260,f256,f166,f99,f158,f252,f90,f248])).

fof(f191,plain,
    ( spl4_14
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f246,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(forward_demodulation,[],[f245,f127])).

fof(f245,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_14 ),
    inference(superposition,[],[f81,f193])).

fof(f193,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f237,plain,
    ( ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_5
    | spl4_14
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f234,f146,f191,f121,f166,f162,f158])).

fof(f234,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_8 ),
    inference(superposition,[],[f72,f148])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f230,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | spl4_7 ),
    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f144,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f144,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_7
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f19])).

fof(f184,plain,(
    spl4_11 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl4_11 ),
    inference(subsumption_resolution,[],[f38,f168])).

fof(f168,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f166])).

fof(f182,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f40,f164])).

fof(f164,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f180,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f47,f160])).

fof(f160,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f149,plain,
    ( ~ spl4_7
    | spl4_8 ),
    inference(avatar_split_clause,[],[f139,f146,f142])).

fof(f139,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f135,f42])).

fof(f135,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f131,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f49,f123])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f121])).

fof(f129,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f119,f125,f121])).

fof(f119,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f41,f62])).

fof(f114,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f61,f105])).

fof(f105,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl4_4
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f110,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f61,f96])).

fof(f96,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_2
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f106,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f87,f103,f99])).

fof(f87,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f57,f49])).

fof(f97,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f86,f94,f90])).

fof(f86,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f57,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:07:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (19870)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (19889)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (19880)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (19873)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (19869)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.52  % (19872)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (19871)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (19895)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (19877)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (19868)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (19879)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (19878)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (19888)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (19884)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.53  % (19876)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (19867)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.54  % (19894)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (19892)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.54  % (19887)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.32/0.54  % (19891)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.54  % (19885)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.55  % (19883)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.55  % (19893)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.55  % (19882)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.55  % (19882)Refutation not found, incomplete strategy% (19882)------------------------------
% 1.32/0.55  % (19882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (19882)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (19882)Memory used [KB]: 10746
% 1.32/0.55  % (19882)Time elapsed: 0.140 s
% 1.32/0.55  % (19882)------------------------------
% 1.32/0.55  % (19882)------------------------------
% 1.32/0.55  % (19874)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.55  % (19875)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.32/0.55  % (19866)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.45/0.56  % (19886)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.56  % (19890)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.45/0.57  % (19879)Refutation found. Thanks to Tanya!
% 1.45/0.57  % SZS status Theorem for theBenchmark
% 1.45/0.57  % (19881)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.45/0.58  % SZS output start Proof for theBenchmark
% 1.45/0.58  fof(f797,plain,(
% 1.45/0.58    $false),
% 1.45/0.58    inference(avatar_sat_refutation,[],[f97,f106,f110,f114,f129,f131,f149,f180,f182,f184,f230,f237,f263,f289,f291,f293,f302,f350,f418,f431,f443,f536,f551,f623,f631,f655,f667,f697,f719,f722,f735,f741,f760,f764,f769,f794])).
% 1.45/0.58  fof(f794,plain,(
% 1.45/0.58    ~spl4_20 | ~spl4_74),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f787])).
% 1.45/0.58  fof(f787,plain,(
% 1.45/0.58    $false | (~spl4_20 | ~spl4_74)),
% 1.45/0.58    inference(subsumption_resolution,[],[f46,f771])).
% 1.45/0.58  fof(f771,plain,(
% 1.45/0.58    sK3 = k2_funct_1(sK2) | (~spl4_20 | ~spl4_74)),
% 1.45/0.58    inference(forward_demodulation,[],[f680,f250])).
% 1.45/0.58  fof(f250,plain,(
% 1.45/0.58    sK2 = k2_funct_1(sK3) | ~spl4_20),
% 1.45/0.58    inference(avatar_component_clause,[],[f248])).
% 1.45/0.58  fof(f248,plain,(
% 1.45/0.58    spl4_20 <=> sK2 = k2_funct_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.45/0.58  fof(f680,plain,(
% 1.45/0.58    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_74),
% 1.45/0.58    inference(avatar_component_clause,[],[f678])).
% 1.45/0.58  fof(f678,plain,(
% 1.45/0.58    spl4_74 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).
% 1.45/0.58  fof(f46,plain,(
% 1.45/0.58    sK3 != k2_funct_1(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f19,plain,(
% 1.45/0.58    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.45/0.58    inference(flattening,[],[f18])).
% 1.45/0.58  fof(f18,plain,(
% 1.45/0.58    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.45/0.58    inference(ennf_transformation,[],[f17])).
% 1.45/0.58  fof(f17,negated_conjecture,(
% 1.45/0.58    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.45/0.58    inference(negated_conjecture,[],[f16])).
% 1.45/0.58  fof(f16,conjecture,(
% 1.45/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.45/0.58  fof(f769,plain,(
% 1.45/0.58    ~spl4_20 | ~spl4_28 | spl4_78),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f768])).
% 1.45/0.58  fof(f768,plain,(
% 1.45/0.58    $false | (~spl4_20 | ~spl4_28 | spl4_78)),
% 1.45/0.58    inference(subsumption_resolution,[],[f360,f766])).
% 1.45/0.58  fof(f766,plain,(
% 1.45/0.58    sK0 != k1_relat_1(sK2) | (~spl4_20 | spl4_78)),
% 1.45/0.58    inference(forward_demodulation,[],[f696,f250])).
% 1.45/0.58  fof(f696,plain,(
% 1.45/0.58    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_78),
% 1.45/0.58    inference(avatar_component_clause,[],[f694])).
% 1.45/0.58  fof(f694,plain,(
% 1.45/0.58    spl4_78 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_78])])).
% 1.45/0.58  fof(f360,plain,(
% 1.45/0.58    sK0 = k1_relat_1(sK2) | ~spl4_28),
% 1.45/0.58    inference(forward_demodulation,[],[f355,f77])).
% 1.45/0.58  fof(f77,plain,(
% 1.45/0.58    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.45/0.58    inference(definition_unfolding,[],[f56,f50])).
% 1.45/0.58  fof(f50,plain,(
% 1.45/0.58    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f12])).
% 1.45/0.58  fof(f12,axiom,(
% 1.45/0.58    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.45/0.58  fof(f56,plain,(
% 1.45/0.58    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.45/0.58    inference(cnf_transformation,[],[f3])).
% 1.45/0.58  fof(f3,axiom,(
% 1.45/0.58    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.45/0.58  fof(f355,plain,(
% 1.45/0.58    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_28),
% 1.45/0.58    inference(superposition,[],[f77,f300])).
% 1.45/0.58  fof(f300,plain,(
% 1.45/0.58    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~spl4_28),
% 1.45/0.58    inference(avatar_component_clause,[],[f298])).
% 1.45/0.58  fof(f298,plain,(
% 1.45/0.58    spl4_28 <=> k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 1.45/0.58  fof(f764,plain,(
% 1.45/0.58    ~spl4_6 | ~spl4_20 | spl4_77),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f763])).
% 1.45/0.58  fof(f763,plain,(
% 1.45/0.58    $false | (~spl4_6 | ~spl4_20 | spl4_77)),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f762])).
% 1.45/0.58  fof(f762,plain,(
% 1.45/0.58    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_6 | ~spl4_20 | spl4_77)),
% 1.45/0.58    inference(forward_demodulation,[],[f761,f127])).
% 1.45/0.58  fof(f127,plain,(
% 1.45/0.58    sK1 = k2_relat_1(sK2) | ~spl4_6),
% 1.45/0.58    inference(avatar_component_clause,[],[f125])).
% 1.45/0.58  fof(f125,plain,(
% 1.45/0.58    spl4_6 <=> sK1 = k2_relat_1(sK2)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.45/0.58  fof(f761,plain,(
% 1.45/0.58    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_20 | spl4_77)),
% 1.45/0.58    inference(forward_demodulation,[],[f692,f250])).
% 1.45/0.58  fof(f692,plain,(
% 1.45/0.58    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_77),
% 1.45/0.58    inference(avatar_component_clause,[],[f690])).
% 1.45/0.58  fof(f690,plain,(
% 1.45/0.58    spl4_77 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_77])])).
% 1.45/0.58  fof(f760,plain,(
% 1.45/0.58    ~spl4_20 | spl4_76),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f759])).
% 1.45/0.58  fof(f759,plain,(
% 1.45/0.58    $false | (~spl4_20 | spl4_76)),
% 1.45/0.58    inference(subsumption_resolution,[],[f43,f743])).
% 1.45/0.58  fof(f743,plain,(
% 1.45/0.58    ~v2_funct_1(sK2) | (~spl4_20 | spl4_76)),
% 1.45/0.58    inference(forward_demodulation,[],[f688,f250])).
% 1.45/0.58  fof(f688,plain,(
% 1.45/0.58    ~v2_funct_1(k2_funct_1(sK3)) | spl4_76),
% 1.45/0.58    inference(avatar_component_clause,[],[f686])).
% 1.45/0.58  fof(f686,plain,(
% 1.45/0.58    spl4_76 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_76])])).
% 1.45/0.58  fof(f43,plain,(
% 1.45/0.58    v2_funct_1(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f741,plain,(
% 1.45/0.58    ~spl4_20 | spl4_75),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f740])).
% 1.45/0.58  fof(f740,plain,(
% 1.45/0.58    $false | (~spl4_20 | spl4_75)),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f61,f49,f736,f57])).
% 1.45/0.58  fof(f57,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f20])).
% 1.45/0.58  fof(f20,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(ennf_transformation,[],[f1])).
% 1.45/0.58  fof(f1,axiom,(
% 1.45/0.58    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.45/0.58  fof(f736,plain,(
% 1.45/0.58    ~v1_relat_1(sK2) | (~spl4_20 | spl4_75)),
% 1.45/0.58    inference(forward_demodulation,[],[f684,f250])).
% 1.45/0.58  fof(f684,plain,(
% 1.45/0.58    ~v1_relat_1(k2_funct_1(sK3)) | spl4_75),
% 1.45/0.58    inference(avatar_component_clause,[],[f682])).
% 1.45/0.58  fof(f682,plain,(
% 1.45/0.58    spl4_75 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_75])])).
% 1.45/0.58  fof(f49,plain,(
% 1.45/0.58    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f61,plain,(
% 1.45/0.58    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f2])).
% 1.45/0.58  fof(f2,axiom,(
% 1.45/0.58    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.45/0.58  fof(f735,plain,(
% 1.45/0.58    ~spl4_20 | spl4_72),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f734])).
% 1.45/0.58  fof(f734,plain,(
% 1.45/0.58    $false | (~spl4_20 | spl4_72)),
% 1.45/0.58    inference(subsumption_resolution,[],[f47,f723])).
% 1.45/0.58  fof(f723,plain,(
% 1.45/0.58    ~v1_funct_1(sK2) | (~spl4_20 | spl4_72)),
% 1.45/0.58    inference(superposition,[],[f671,f250])).
% 1.45/0.58  fof(f671,plain,(
% 1.45/0.58    ~v1_funct_1(k2_funct_1(sK3)) | spl4_72),
% 1.45/0.58    inference(avatar_component_clause,[],[f669])).
% 1.45/0.58  fof(f669,plain,(
% 1.45/0.58    spl4_72 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_72])])).
% 1.45/0.58  fof(f47,plain,(
% 1.45/0.58    v1_funct_1(sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f722,plain,(
% 1.45/0.58    spl4_22 | ~spl4_42),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f721])).
% 1.45/0.58  fof(f721,plain,(
% 1.45/0.58    $false | (spl4_22 | ~spl4_42)),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f720])).
% 1.45/0.58  fof(f720,plain,(
% 1.45/0.58    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_22 | ~spl4_42)),
% 1.45/0.58    inference(forward_demodulation,[],[f258,f441])).
% 1.45/0.58  fof(f441,plain,(
% 1.45/0.58    sK0 = k2_relat_1(sK3) | ~spl4_42),
% 1.45/0.58    inference(avatar_component_clause,[],[f439])).
% 1.45/0.58  fof(f439,plain,(
% 1.45/0.58    spl4_42 <=> sK0 = k2_relat_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.45/0.58  fof(f258,plain,(
% 1.45/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_22),
% 1.45/0.58    inference(avatar_component_clause,[],[f256])).
% 1.45/0.58  fof(f256,plain,(
% 1.45/0.58    spl4_22 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.45/0.58  fof(f719,plain,(
% 1.45/0.58    spl4_23 | ~spl4_71),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f718])).
% 1.45/0.58  fof(f718,plain,(
% 1.45/0.58    $false | (spl4_23 | ~spl4_71)),
% 1.45/0.58    inference(subsumption_resolution,[],[f262,f716])).
% 1.45/0.58  fof(f716,plain,(
% 1.45/0.58    sK1 = k1_relat_1(sK3) | ~spl4_71),
% 1.45/0.58    inference(forward_demodulation,[],[f706,f77])).
% 1.45/0.58  fof(f706,plain,(
% 1.45/0.58    k1_relat_1(sK3) = k2_relat_1(k6_partfun1(sK1)) | ~spl4_71),
% 1.45/0.58    inference(superposition,[],[f77,f665])).
% 1.45/0.58  fof(f665,plain,(
% 1.45/0.58    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~spl4_71),
% 1.45/0.58    inference(avatar_component_clause,[],[f663])).
% 1.45/0.58  fof(f663,plain,(
% 1.45/0.58    spl4_71 <=> k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_71])])).
% 1.45/0.58  fof(f262,plain,(
% 1.45/0.58    sK1 != k1_relat_1(sK3) | spl4_23),
% 1.45/0.58    inference(avatar_component_clause,[],[f260])).
% 1.45/0.58  fof(f260,plain,(
% 1.45/0.58    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.45/0.58  fof(f697,plain,(
% 1.45/0.58    spl4_74 | ~spl4_75 | ~spl4_76 | ~spl4_11 | ~spl4_1 | ~spl4_72 | ~spl4_77 | ~spl4_78 | ~spl4_42 | ~spl4_56),
% 1.45/0.58    inference(avatar_split_clause,[],[f676,f529,f439,f694,f690,f669,f90,f166,f686,f682,f678])).
% 1.45/0.58  fof(f166,plain,(
% 1.45/0.58    spl4_11 <=> v1_funct_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.45/0.58  fof(f90,plain,(
% 1.45/0.58    spl4_1 <=> v1_relat_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.45/0.58  fof(f529,plain,(
% 1.45/0.58    spl4_56 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.45/0.58  fof(f676,plain,(
% 1.45/0.58    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_42 | ~spl4_56)),
% 1.45/0.58    inference(forward_demodulation,[],[f661,f441])).
% 1.45/0.58  fof(f661,plain,(
% 1.45/0.58    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_56),
% 1.45/0.58    inference(superposition,[],[f81,f531])).
% 1.45/0.58  fof(f531,plain,(
% 1.45/0.58    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_56),
% 1.45/0.58    inference(avatar_component_clause,[],[f529])).
% 1.45/0.58  fof(f81,plain,(
% 1.45/0.58    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.45/0.58    inference(definition_unfolding,[],[f60,f50])).
% 1.45/0.58  fof(f60,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_funct_1(X0) = X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f24])).
% 1.45/0.58  fof(f24,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f23])).
% 1.45/0.58  fof(f23,plain,(
% 1.45/0.58    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f6])).
% 1.45/0.58  fof(f6,axiom,(
% 1.45/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.45/0.58  fof(f667,plain,(
% 1.45/0.58    ~spl4_1 | ~spl4_21 | ~spl4_11 | spl4_71 | ~spl4_56),
% 1.45/0.58    inference(avatar_split_clause,[],[f659,f529,f663,f166,f252,f90])).
% 1.45/0.58  fof(f252,plain,(
% 1.45/0.58    spl4_21 <=> v2_funct_1(sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.45/0.58  fof(f659,plain,(
% 1.45/0.58    k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_56),
% 1.45/0.58    inference(superposition,[],[f80,f531])).
% 1.45/0.58  fof(f80,plain,(
% 1.45/0.58    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.45/0.58    inference(definition_unfolding,[],[f58,f50])).
% 1.45/0.58  fof(f58,plain,(
% 1.45/0.58    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f22])).
% 1.45/0.58  fof(f22,plain,(
% 1.45/0.58    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.45/0.58    inference(flattening,[],[f21])).
% 1.45/0.58  fof(f21,plain,(
% 1.45/0.58    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.45/0.58    inference(ennf_transformation,[],[f5])).
% 1.45/0.58  fof(f5,axiom,(
% 1.45/0.58    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.45/0.58  fof(f655,plain,(
% 1.45/0.58    ~spl4_57),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f632])).
% 1.45/0.58  fof(f632,plain,(
% 1.45/0.58    $false | ~spl4_57),
% 1.45/0.58    inference(subsumption_resolution,[],[f44,f535])).
% 1.45/0.58  fof(f535,plain,(
% 1.45/0.58    k1_xboole_0 = sK0 | ~spl4_57),
% 1.45/0.58    inference(avatar_component_clause,[],[f533])).
% 1.45/0.58  fof(f533,plain,(
% 1.45/0.58    spl4_57 <=> k1_xboole_0 = sK0),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.45/0.58  fof(f44,plain,(
% 1.45/0.58    k1_xboole_0 != sK0),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f631,plain,(
% 1.45/0.58    spl4_69),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f628])).
% 1.45/0.58  fof(f628,plain,(
% 1.45/0.58    $false | spl4_69),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f75,f622])).
% 1.45/0.58  fof(f622,plain,(
% 1.45/0.58    ~v2_funct_1(k6_partfun1(sK0)) | spl4_69),
% 1.45/0.58    inference(avatar_component_clause,[],[f620])).
% 1.45/0.58  fof(f620,plain,(
% 1.45/0.58    spl4_69 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_69])])).
% 1.45/0.58  fof(f75,plain,(
% 1.45/0.58    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.45/0.58    inference(definition_unfolding,[],[f52,f50])).
% 1.45/0.58  fof(f52,plain,(
% 1.45/0.58    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f4])).
% 1.45/0.58  fof(f4,axiom,(
% 1.45/0.58    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.45/0.58  fof(f623,plain,(
% 1.45/0.58    ~spl4_40 | ~spl4_10 | ~spl4_11 | spl4_57 | spl4_21 | ~spl4_69 | ~spl4_8 | ~spl4_59),
% 1.45/0.58    inference(avatar_split_clause,[],[f616,f549,f146,f620,f252,f533,f166,f162,f415])).
% 1.45/0.58  fof(f415,plain,(
% 1.45/0.58    spl4_40 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.45/0.58  fof(f162,plain,(
% 1.45/0.58    spl4_10 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.45/0.58  fof(f146,plain,(
% 1.45/0.58    spl4_8 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.45/0.58  fof(f549,plain,(
% 1.45/0.58    spl4_59 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.45/0.58  fof(f616,plain,(
% 1.45/0.58    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_8 | ~spl4_59)),
% 1.45/0.58    inference(superposition,[],[f550,f148])).
% 1.45/0.58  fof(f148,plain,(
% 1.45/0.58    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_8),
% 1.45/0.58    inference(avatar_component_clause,[],[f146])).
% 1.45/0.58  fof(f550,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_59),
% 1.45/0.58    inference(avatar_component_clause,[],[f549])).
% 1.45/0.58  fof(f551,plain,(
% 1.45/0.58    ~spl4_9 | spl4_59 | ~spl4_5 | ~spl4_27),
% 1.45/0.58    inference(avatar_split_clause,[],[f547,f286,f121,f549,f158])).
% 1.45/0.58  fof(f158,plain,(
% 1.45/0.58    spl4_9 <=> v1_funct_1(sK2)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.45/0.58  fof(f121,plain,(
% 1.45/0.58    spl4_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.45/0.58  fof(f286,plain,(
% 1.45/0.58    spl4_27 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.45/0.58  fof(f547,plain,(
% 1.45/0.58    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f542])).
% 1.45/0.58  fof(f542,plain,(
% 1.45/0.58    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.45/0.58    inference(superposition,[],[f69,f41])).
% 1.45/0.58  fof(f41,plain,(
% 1.45/0.58    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f69,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f31])).
% 1.45/0.58  fof(f31,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.45/0.58    inference(flattening,[],[f30])).
% 1.45/0.58  fof(f30,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.45/0.58    inference(ennf_transformation,[],[f14])).
% 1.45/0.58  fof(f14,axiom,(
% 1.45/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.45/0.58  fof(f536,plain,(
% 1.45/0.58    spl4_56 | spl4_57 | ~spl4_21 | ~spl4_11 | ~spl4_10 | ~spl4_40 | ~spl4_39),
% 1.45/0.58    inference(avatar_split_clause,[],[f436,f411,f415,f162,f166,f252,f533,f529])).
% 1.45/0.58  fof(f411,plain,(
% 1.45/0.58    spl4_39 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 1.45/0.58  fof(f436,plain,(
% 1.45/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_39),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f434])).
% 1.45/0.58  fof(f434,plain,(
% 1.45/0.58    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_39),
% 1.45/0.58    inference(superposition,[],[f63,f413])).
% 1.45/0.58  fof(f413,plain,(
% 1.45/0.58    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_39),
% 1.45/0.58    inference(avatar_component_clause,[],[f411])).
% 1.45/0.58  fof(f63,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f27])).
% 1.45/0.58  fof(f27,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.58    inference(flattening,[],[f26])).
% 1.45/0.58  fof(f26,plain,(
% 1.45/0.58    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.58    inference(ennf_transformation,[],[f15])).
% 1.45/0.58  fof(f15,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.45/0.58  fof(f443,plain,(
% 1.45/0.58    ~spl4_10 | spl4_42 | ~spl4_39),
% 1.45/0.58    inference(avatar_split_clause,[],[f435,f411,f439,f162])).
% 1.45/0.58  fof(f435,plain,(
% 1.45/0.58    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_39),
% 1.45/0.58    inference(superposition,[],[f62,f413])).
% 1.45/0.58  fof(f62,plain,(
% 1.45/0.58    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.45/0.58    inference(cnf_transformation,[],[f25])).
% 1.45/0.58  fof(f25,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.58    inference(ennf_transformation,[],[f7])).
% 1.45/0.58  fof(f7,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.45/0.58  fof(f431,plain,(
% 1.45/0.58    spl4_40),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f430])).
% 1.45/0.58  fof(f430,plain,(
% 1.45/0.58    $false | spl4_40),
% 1.45/0.58    inference(subsumption_resolution,[],[f39,f417])).
% 1.45/0.58  fof(f417,plain,(
% 1.45/0.58    ~v1_funct_2(sK3,sK1,sK0) | spl4_40),
% 1.45/0.58    inference(avatar_component_clause,[],[f415])).
% 1.45/0.58  fof(f39,plain,(
% 1.45/0.58    v1_funct_2(sK3,sK1,sK0)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f418,plain,(
% 1.45/0.58    spl4_39 | ~spl4_11 | ~spl4_5 | ~spl4_27 | ~spl4_9 | ~spl4_10 | ~spl4_40),
% 1.45/0.58    inference(avatar_split_clause,[],[f405,f415,f162,f158,f286,f121,f166,f411])).
% 1.45/0.58  fof(f405,plain,(
% 1.45/0.58    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.45/0.58    inference(resolution,[],[f65,f42])).
% 1.45/0.58  fof(f42,plain,(
% 1.45/0.58    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f65,plain,(
% 1.45/0.58    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.45/0.58    inference(cnf_transformation,[],[f29])).
% 1.45/0.58  fof(f29,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.45/0.58    inference(flattening,[],[f28])).
% 1.45/0.58  fof(f28,plain,(
% 1.45/0.58    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.45/0.58    inference(ennf_transformation,[],[f13])).
% 1.45/0.58  fof(f13,axiom,(
% 1.45/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.45/0.58  fof(f350,plain,(
% 1.45/0.58    ~spl4_25),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f338])).
% 1.45/0.58  fof(f338,plain,(
% 1.45/0.58    $false | ~spl4_25),
% 1.45/0.58    inference(subsumption_resolution,[],[f45,f280])).
% 1.45/0.58  fof(f280,plain,(
% 1.45/0.58    k1_xboole_0 = sK1 | ~spl4_25),
% 1.45/0.58    inference(avatar_component_clause,[],[f278])).
% 1.45/0.58  fof(f278,plain,(
% 1.45/0.58    spl4_25 <=> k1_xboole_0 = sK1),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.45/0.58  fof(f45,plain,(
% 1.45/0.58    k1_xboole_0 != sK1),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f302,plain,(
% 1.45/0.58    ~spl4_3 | ~spl4_26 | ~spl4_9 | spl4_28 | ~spl4_24),
% 1.45/0.58    inference(avatar_split_clause,[],[f295,f274,f298,f158,f282,f99])).
% 1.45/0.58  fof(f99,plain,(
% 1.45/0.58    spl4_3 <=> v1_relat_1(sK2)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.45/0.58  fof(f282,plain,(
% 1.45/0.58    spl4_26 <=> v2_funct_1(sK2)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.45/0.58  fof(f274,plain,(
% 1.45/0.58    spl4_24 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.45/0.58  fof(f295,plain,(
% 1.45/0.58    k6_partfun1(sK0) = k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_24),
% 1.45/0.58    inference(superposition,[],[f80,f276])).
% 1.45/0.58  fof(f276,plain,(
% 1.45/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_24),
% 1.45/0.58    inference(avatar_component_clause,[],[f274])).
% 1.45/0.58  fof(f293,plain,(
% 1.45/0.58    spl4_27),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f292])).
% 1.45/0.58  fof(f292,plain,(
% 1.45/0.58    $false | spl4_27),
% 1.45/0.58    inference(subsumption_resolution,[],[f48,f288])).
% 1.45/0.58  fof(f288,plain,(
% 1.45/0.58    ~v1_funct_2(sK2,sK0,sK1) | spl4_27),
% 1.45/0.58    inference(avatar_component_clause,[],[f286])).
% 1.45/0.58  fof(f48,plain,(
% 1.45/0.58    v1_funct_2(sK2,sK0,sK1)),
% 1.45/0.58    inference(cnf_transformation,[],[f19])).
% 1.45/0.58  fof(f291,plain,(
% 1.45/0.58    spl4_26),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f290])).
% 1.45/0.58  fof(f290,plain,(
% 1.45/0.58    $false | spl4_26),
% 1.45/0.58    inference(subsumption_resolution,[],[f43,f284])).
% 1.45/0.58  fof(f284,plain,(
% 1.45/0.58    ~v2_funct_1(sK2) | spl4_26),
% 1.45/0.58    inference(avatar_component_clause,[],[f282])).
% 1.45/0.58  fof(f289,plain,(
% 1.45/0.58    spl4_24 | spl4_25 | ~spl4_26 | ~spl4_9 | ~spl4_5 | ~spl4_27),
% 1.45/0.58    inference(avatar_split_clause,[],[f272,f286,f121,f158,f282,f278,f274])).
% 1.45/0.58  fof(f272,plain,(
% 1.45/0.58    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.45/0.58    inference(trivial_inequality_removal,[],[f269])).
% 1.45/0.58  fof(f269,plain,(
% 1.45/0.58    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.45/0.58    inference(superposition,[],[f63,f41])).
% 1.45/0.58  fof(f263,plain,(
% 1.45/0.58    spl4_20 | ~spl4_1 | ~spl4_21 | ~spl4_9 | ~spl4_3 | ~spl4_11 | ~spl4_22 | ~spl4_23 | ~spl4_6 | ~spl4_14),
% 1.45/0.58    inference(avatar_split_clause,[],[f246,f191,f125,f260,f256,f166,f99,f158,f252,f90,f248])).
% 1.45/0.58  fof(f191,plain,(
% 1.45/0.58    spl4_14 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.45/0.58    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.45/0.58  fof(f246,plain,(
% 1.45/0.58    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_6 | ~spl4_14)),
% 1.45/0.58    inference(forward_demodulation,[],[f245,f127])).
% 1.45/0.58  fof(f245,plain,(
% 1.45/0.58    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_14),
% 1.45/0.58    inference(superposition,[],[f81,f193])).
% 1.45/0.58  fof(f193,plain,(
% 1.45/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_14),
% 1.45/0.58    inference(avatar_component_clause,[],[f191])).
% 1.45/0.58  fof(f237,plain,(
% 1.45/0.58    ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_5 | spl4_14 | ~spl4_8),
% 1.45/0.58    inference(avatar_split_clause,[],[f234,f146,f191,f121,f166,f162,f158])).
% 1.45/0.58  fof(f234,plain,(
% 1.45/0.58    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_8),
% 1.45/0.58    inference(superposition,[],[f72,f148])).
% 1.45/0.58  fof(f72,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f35])).
% 1.45/0.58  fof(f35,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.45/0.58    inference(flattening,[],[f34])).
% 1.45/0.58  fof(f34,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.45/0.58    inference(ennf_transformation,[],[f11])).
% 1.45/0.58  fof(f11,axiom,(
% 1.45/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.45/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.45/0.58  fof(f230,plain,(
% 1.45/0.58    spl4_7),
% 1.45/0.58    inference(avatar_contradiction_clause,[],[f219])).
% 1.45/0.58  fof(f219,plain,(
% 1.45/0.58    $false | spl4_7),
% 1.45/0.58    inference(unit_resulting_resolution,[],[f47,f38,f40,f49,f144,f74])).
% 1.45/0.58  fof(f74,plain,(
% 1.45/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.45/0.58    inference(cnf_transformation,[],[f37])).
% 1.45/0.58  fof(f37,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.45/0.58    inference(flattening,[],[f36])).
% 1.45/0.58  fof(f36,plain,(
% 1.45/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.45/0.58    inference(ennf_transformation,[],[f9])).
% 1.45/0.59  fof(f9,axiom,(
% 1.45/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.45/0.59  fof(f144,plain,(
% 1.45/0.59    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_7),
% 1.45/0.59    inference(avatar_component_clause,[],[f142])).
% 1.45/0.59  fof(f142,plain,(
% 1.45/0.59    spl4_7 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.45/0.59  fof(f40,plain,(
% 1.45/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f38,plain,(
% 1.45/0.59    v1_funct_1(sK3)),
% 1.45/0.59    inference(cnf_transformation,[],[f19])).
% 1.45/0.59  fof(f184,plain,(
% 1.45/0.59    spl4_11),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f183])).
% 1.45/0.59  fof(f183,plain,(
% 1.45/0.59    $false | spl4_11),
% 1.45/0.59    inference(subsumption_resolution,[],[f38,f168])).
% 1.45/0.59  fof(f168,plain,(
% 1.45/0.59    ~v1_funct_1(sK3) | spl4_11),
% 1.45/0.59    inference(avatar_component_clause,[],[f166])).
% 1.45/0.59  fof(f182,plain,(
% 1.45/0.59    spl4_10),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f181])).
% 1.45/0.59  fof(f181,plain,(
% 1.45/0.59    $false | spl4_10),
% 1.45/0.59    inference(subsumption_resolution,[],[f40,f164])).
% 1.45/0.59  fof(f164,plain,(
% 1.45/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_10),
% 1.45/0.59    inference(avatar_component_clause,[],[f162])).
% 1.45/0.59  fof(f180,plain,(
% 1.45/0.59    spl4_9),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f179])).
% 1.45/0.59  fof(f179,plain,(
% 1.45/0.59    $false | spl4_9),
% 1.45/0.59    inference(subsumption_resolution,[],[f47,f160])).
% 1.45/0.59  fof(f160,plain,(
% 1.45/0.59    ~v1_funct_1(sK2) | spl4_9),
% 1.45/0.59    inference(avatar_component_clause,[],[f158])).
% 1.45/0.59  fof(f149,plain,(
% 1.45/0.59    ~spl4_7 | spl4_8),
% 1.45/0.59    inference(avatar_split_clause,[],[f139,f146,f142])).
% 1.45/0.59  fof(f139,plain,(
% 1.45/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.45/0.59    inference(resolution,[],[f135,f42])).
% 1.45/0.59  fof(f135,plain,(
% 1.45/0.59    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.45/0.59    inference(resolution,[],[f71,f54])).
% 1.45/0.59  fof(f54,plain,(
% 1.45/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.45/0.59    inference(cnf_transformation,[],[f10])).
% 1.45/0.59  fof(f10,axiom,(
% 1.45/0.59    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.45/0.59  fof(f71,plain,(
% 1.45/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.45/0.59    inference(cnf_transformation,[],[f33])).
% 1.45/0.59  fof(f33,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.45/0.59    inference(flattening,[],[f32])).
% 1.45/0.59  fof(f32,plain,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.45/0.59    inference(ennf_transformation,[],[f8])).
% 1.45/0.59  fof(f8,axiom,(
% 1.45/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.45/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.45/0.59  fof(f131,plain,(
% 1.45/0.59    spl4_5),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f130])).
% 1.45/0.59  fof(f130,plain,(
% 1.45/0.59    $false | spl4_5),
% 1.45/0.59    inference(subsumption_resolution,[],[f49,f123])).
% 1.45/0.59  fof(f123,plain,(
% 1.45/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_5),
% 1.45/0.59    inference(avatar_component_clause,[],[f121])).
% 1.45/0.59  fof(f129,plain,(
% 1.45/0.59    ~spl4_5 | spl4_6),
% 1.45/0.59    inference(avatar_split_clause,[],[f119,f125,f121])).
% 1.45/0.59  fof(f119,plain,(
% 1.45/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.45/0.59    inference(superposition,[],[f41,f62])).
% 1.45/0.59  fof(f114,plain,(
% 1.45/0.59    spl4_4),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f111])).
% 1.45/0.59  fof(f111,plain,(
% 1.45/0.59    $false | spl4_4),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f61,f105])).
% 1.45/0.59  fof(f105,plain,(
% 1.45/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_4),
% 1.45/0.59    inference(avatar_component_clause,[],[f103])).
% 1.45/0.59  fof(f103,plain,(
% 1.45/0.59    spl4_4 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.45/0.59  fof(f110,plain,(
% 1.45/0.59    spl4_2),
% 1.45/0.59    inference(avatar_contradiction_clause,[],[f107])).
% 1.45/0.59  fof(f107,plain,(
% 1.45/0.59    $false | spl4_2),
% 1.45/0.59    inference(unit_resulting_resolution,[],[f61,f96])).
% 1.45/0.59  fof(f96,plain,(
% 1.45/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_2),
% 1.45/0.59    inference(avatar_component_clause,[],[f94])).
% 1.45/0.59  fof(f94,plain,(
% 1.45/0.59    spl4_2 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.45/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.45/0.59  fof(f106,plain,(
% 1.45/0.59    spl4_3 | ~spl4_4),
% 1.45/0.59    inference(avatar_split_clause,[],[f87,f103,f99])).
% 1.45/0.59  fof(f87,plain,(
% 1.45/0.59    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.45/0.59    inference(resolution,[],[f57,f49])).
% 1.45/0.59  fof(f97,plain,(
% 1.45/0.59    spl4_1 | ~spl4_2),
% 1.45/0.59    inference(avatar_split_clause,[],[f86,f94,f90])).
% 1.45/0.59  fof(f86,plain,(
% 1.45/0.59    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.45/0.59    inference(resolution,[],[f57,f40])).
% 1.45/0.59  % SZS output end Proof for theBenchmark
% 1.45/0.59  % (19879)------------------------------
% 1.45/0.59  % (19879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.59  % (19879)Termination reason: Refutation
% 1.45/0.59  
% 1.45/0.59  % (19879)Memory used [KB]: 6780
% 1.45/0.59  % (19879)Time elapsed: 0.141 s
% 1.45/0.59  % (19879)------------------------------
% 1.45/0.59  % (19879)------------------------------
% 1.45/0.60  % (19865)Success in time 0.233 s
%------------------------------------------------------------------------------
