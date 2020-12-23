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
% DateTime   : Thu Dec  3 13:02:42 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 532 expanded)
%              Number of leaves         :   53 ( 195 expanded)
%              Depth                    :   11
%              Number of atoms          :  870 (2592 expanded)
%              Number of equality atoms :  179 ( 732 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f872,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f114,f129,f131,f155,f213,f215,f217,f231,f244,f297,f301,f322,f324,f332,f356,f416,f441,f483,f490,f515,f516,f527,f555,f569,f591,f594,f597,f607,f747,f794,f802,f826,f830,f834,f871])).

fof(f871,plain,
    ( ~ spl4_20
    | ~ spl4_55 ),
    inference(avatar_contradiction_clause,[],[f859])).

fof(f859,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_55 ),
    inference(subsumption_resolution,[],[f52,f837])).

fof(f837,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_20
    | ~ spl4_55 ),
    inference(forward_demodulation,[],[f574,f284])).

fof(f284,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl4_20
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f574,plain,
    ( sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_55 ),
    inference(avatar_component_clause,[],[f572])).

fof(f572,plain,
    ( spl4_55
  <=> sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).

fof(f52,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f834,plain,
    ( ~ spl4_2
    | ~ spl4_20
    | spl4_58 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_20
    | spl4_58 ),
    inference(trivial_inequality_removal,[],[f832])).

fof(f832,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ spl4_2
    | ~ spl4_20
    | spl4_58 ),
    inference(forward_demodulation,[],[f831,f110])).

fof(f110,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_2
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f831,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | ~ spl4_20
    | spl4_58 ),
    inference(forward_demodulation,[],[f586,f284])).

fof(f586,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | spl4_58 ),
    inference(avatar_component_clause,[],[f584])).

fof(f584,plain,
    ( spl4_58
  <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).

fof(f830,plain,
    ( ~ spl4_20
    | spl4_56 ),
    inference(avatar_contradiction_clause,[],[f829])).

fof(f829,plain,
    ( $false
    | ~ spl4_20
    | spl4_56 ),
    inference(subsumption_resolution,[],[f49,f828])).

fof(f828,plain,
    ( ~ v2_funct_1(sK2)
    | ~ spl4_20
    | spl4_56 ),
    inference(forward_demodulation,[],[f578,f284])).

fof(f578,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | spl4_56 ),
    inference(avatar_component_clause,[],[f576])).

fof(f576,plain,
    ( spl4_56
  <=> v2_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).

fof(f49,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f826,plain,
    ( ~ spl4_20
    | ~ spl4_36
    | spl4_59 ),
    inference(avatar_contradiction_clause,[],[f825])).

fof(f825,plain,
    ( $false
    | ~ spl4_20
    | ~ spl4_36
    | spl4_59 ),
    inference(subsumption_resolution,[],[f415,f810])).

fof(f810,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_20
    | spl4_59 ),
    inference(superposition,[],[f590,f284])).

fof(f590,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | spl4_59 ),
    inference(avatar_component_clause,[],[f588])).

fof(f588,plain,
    ( spl4_59
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f415,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f413])).

fof(f413,plain,
    ( spl4_36
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f802,plain,(
    spl4_85 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | spl4_85 ),
    inference(unit_resulting_resolution,[],[f83,f793])).

fof(f793,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_85 ),
    inference(avatar_component_clause,[],[f791])).

fof(f791,plain,
    ( spl4_85
  <=> v2_funct_1(k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f83,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f56])).

fof(f56,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f794,plain,
    ( ~ spl4_45
    | ~ spl4_9
    | ~ spl4_10
    | spl4_49
    | spl4_21
    | ~ spl4_85
    | ~ spl4_7
    | ~ spl4_60 ),
    inference(avatar_split_clause,[],[f787,f605,f152,f791,f286,f507,f199,f195,f480])).

fof(f480,plain,
    ( spl4_45
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f195,plain,
    ( spl4_9
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f199,plain,
    ( spl4_10
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f507,plain,
    ( spl4_49
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f286,plain,
    ( spl4_21
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f152,plain,
    ( spl4_7
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f605,plain,
    ( spl4_60
  <=> ! [X1,X0] :
        ( ~ v1_funct_1(X0)
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f787,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_7
    | ~ spl4_60 ),
    inference(superposition,[],[f606,f154])).

fof(f154,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f606,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0))
        | v2_funct_1(X0)
        | k1_xboole_0 = X1
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1)))
        | ~ v1_funct_2(X0,sK1,X1) )
    | ~ spl4_60 ),
    inference(avatar_component_clause,[],[f605])).

fof(f747,plain,(
    spl4_57 ),
    inference(avatar_contradiction_clause,[],[f745])).

fof(f745,plain,
    ( $false
    | spl4_57 ),
    inference(unit_resulting_resolution,[],[f92,f44,f582,f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f582,plain,
    ( ~ v1_funct_1(k2_funct_1(sK3))
    | spl4_57 ),
    inference(avatar_component_clause,[],[f580])).

fof(f580,plain,
    ( spl4_57
  <=> v1_funct_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f44,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f21])).

fof(f92,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f68,f46])).

fof(f46,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f607,plain,
    ( ~ spl4_8
    | spl4_60
    | ~ spl4_1
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f603,f319,f104,f605,f191])).

fof(f191,plain,
    ( spl4_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f104,plain,
    ( spl4_1
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f319,plain,
    ( spl4_27
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f603,plain,(
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
    inference(trivial_inequality_removal,[],[f598])).

fof(f598,plain,(
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
    inference(superposition,[],[f76,f47])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f597,plain,
    ( spl4_22
    | ~ spl4_47 ),
    inference(avatar_contradiction_clause,[],[f596])).

fof(f596,plain,
    ( $false
    | spl4_22
    | ~ spl4_47 ),
    inference(trivial_inequality_removal,[],[f595])).

fof(f595,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | spl4_22
    | ~ spl4_47 ),
    inference(forward_demodulation,[],[f292,f500])).

fof(f500,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f498])).

fof(f498,plain,
    ( spl4_47
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f292,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f290])).

fof(f290,plain,
    ( spl4_22
  <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f594,plain,(
    spl4_54 ),
    inference(avatar_contradiction_clause,[],[f592])).

fof(f592,plain,
    ( $false
    | spl4_54 ),
    inference(unit_resulting_resolution,[],[f92,f44,f568,f64])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f568,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | spl4_54 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl4_54
  <=> v1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f591,plain,
    ( spl4_55
    | ~ spl4_54
    | ~ spl4_56
    | ~ spl4_10
    | ~ spl4_15
    | ~ spl4_57
    | ~ spl4_58
    | ~ spl4_59
    | ~ spl4_47
    | ~ spl4_50 ),
    inference(avatar_split_clause,[],[f570,f512,f498,f588,f584,f580,f257,f199,f576,f566,f572])).

fof(f257,plain,
    ( spl4_15
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f512,plain,
    ( spl4_50
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f570,plain,
    ( sK0 != k1_relat_1(k2_funct_1(sK3))
    | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_47
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f560,f500])).

fof(f560,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k2_funct_1(sK3))
    | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ spl4_50 ),
    inference(superposition,[],[f87,f514])).

fof(f514,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f512])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f66,f56])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
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
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f569,plain,
    ( ~ spl4_54
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_10
    | spl4_23
    | ~ spl4_47
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(avatar_split_clause,[],[f564,f524,f512,f498,f294,f199,f286,f257,f566])).

fof(f294,plain,
    ( spl4_23
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f524,plain,
    ( spl4_52
  <=> k1_relat_1(sK3) = k10_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).

fof(f564,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_47
    | ~ spl4_50
    | ~ spl4_52 ),
    inference(forward_demodulation,[],[f563,f526])).

fof(f526,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ spl4_52 ),
    inference(avatar_component_clause,[],[f524])).

fof(f563,plain,
    ( sK1 = k10_relat_1(sK3,sK0)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_47
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f562,f500])).

fof(f562,plain,
    ( sK1 = k10_relat_1(sK3,k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_50 ),
    inference(forward_demodulation,[],[f561,f85])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f56])).

fof(f61,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f561,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_50 ),
    inference(duplicate_literal_removal,[],[f559])).

fof(f559,plain,
    ( k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_partfun1(sK1))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_50 ),
    inference(superposition,[],[f136,f514])).

fof(f136,plain,(
    ! [X2,X3] :
      ( k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(k2_funct_1(X2))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f67,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f555,plain,(
    ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f538])).

fof(f538,plain,
    ( $false
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f50,f509])).

fof(f509,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f507])).

fof(f50,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f21])).

fof(f527,plain,
    ( ~ spl4_15
    | spl4_52
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f518,f498,f524,f257])).

fof(f518,plain,
    ( k1_relat_1(sK3) = k10_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_47 ),
    inference(superposition,[],[f62,f500])).

fof(f62,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f516,plain,
    ( ~ spl4_9
    | spl4_47
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f494,f476,f498,f195])).

fof(f476,plain,
    ( spl4_44
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f494,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_44 ),
    inference(superposition,[],[f69,f478])).

fof(f478,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f476])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f515,plain,
    ( spl4_50
    | spl4_49
    | ~ spl4_21
    | ~ spl4_10
    | ~ spl4_9
    | ~ spl4_45
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f495,f476,f480,f195,f199,f286,f507,f512])).

fof(f495,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_44 ),
    inference(trivial_inequality_removal,[],[f493])).

fof(f493,plain,
    ( sK0 != sK0
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_44 ),
    inference(superposition,[],[f70,f478])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f490,plain,(
    spl4_45 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | spl4_45 ),
    inference(subsumption_resolution,[],[f45,f482])).

fof(f482,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_45 ),
    inference(avatar_component_clause,[],[f480])).

fof(f45,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f483,plain,
    ( spl4_44
    | ~ spl4_10
    | ~ spl4_1
    | ~ spl4_27
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f471,f480,f195,f191,f319,f104,f199,f476])).

fof(f471,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f441,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl4_32 ),
    inference(unit_resulting_resolution,[],[f93,f53,f392,f64])).

fof(f392,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f390])).

fof(f390,plain,
    ( spl4_32
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f68,f55])).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f416,plain,
    ( ~ spl4_32
    | ~ spl4_3
    | ~ spl4_26
    | ~ spl4_8
    | spl4_36
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f411,f307,f126,f108,f413,f191,f315,f118,f390])).

fof(f118,plain,
    ( spl4_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f315,plain,
    ( spl4_26
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f126,plain,
    ( spl4_5
  <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f307,plain,
    ( spl4_24
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f411,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f410,f128])).

fof(f128,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f126])).

fof(f410,plain,
    ( sK0 = k10_relat_1(sK2,sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f409,f110])).

fof(f409,plain,
    ( sK0 = k10_relat_1(sK2,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(forward_demodulation,[],[f388,f85])).

fof(f388,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(superposition,[],[f136,f309])).

fof(f309,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f307])).

fof(f356,plain,(
    ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f342])).

fof(f342,plain,
    ( $false
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f51,f313])).

fof(f313,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f51,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f21])).

fof(f332,plain,(
    spl4_27 ),
    inference(avatar_contradiction_clause,[],[f331])).

fof(f331,plain,
    ( $false
    | spl4_27 ),
    inference(subsumption_resolution,[],[f54,f321])).

fof(f321,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_27 ),
    inference(avatar_component_clause,[],[f319])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f324,plain,(
    spl4_26 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl4_26 ),
    inference(subsumption_resolution,[],[f49,f317])).

fof(f317,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_26 ),
    inference(avatar_component_clause,[],[f315])).

fof(f322,plain,
    ( spl4_24
    | spl4_25
    | ~ spl4_26
    | ~ spl4_8
    | ~ spl4_1
    | ~ spl4_27 ),
    inference(avatar_split_clause,[],[f305,f319,f104,f191,f315,f311,f307])).

fof(f305,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(trivial_inequality_removal,[],[f302])).

fof(f302,plain,
    ( sK1 != sK1
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(superposition,[],[f70,f47])).

fof(f301,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f92,f259])).

fof(f259,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f257])).

fof(f297,plain,
    ( spl4_20
    | ~ spl4_15
    | ~ spl4_21
    | ~ spl4_8
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_22
    | ~ spl4_23
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f280,f234,f108,f294,f290,f199,f118,f191,f286,f257,f282])).

fof(f234,plain,
    ( spl4_13
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f280,plain,
    ( sK1 != k1_relat_1(sK3)
    | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f255,f110])).

fof(f255,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_13 ),
    inference(superposition,[],[f87,f236])).

fof(f236,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f234])).

fof(f244,plain,
    ( ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_1
    | spl4_13
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f241,f152,f234,f104,f199,f195,f191])).

fof(f241,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7 ),
    inference(superposition,[],[f79,f154])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f231,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f150,f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f150,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl4_6
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f217,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f44,f201])).

fof(f201,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f215,plain,(
    spl4_9 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | spl4_9 ),
    inference(subsumption_resolution,[],[f46,f197])).

fof(f197,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f195])).

fof(f213,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f212])).

fof(f212,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f53,f193])).

fof(f193,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f191])).

fof(f155,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f145,f152,f148])).

fof(f145,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f139,f48])).

fof(f139,plain,(
    ! [X2,X1] :
      ( ~ r2_relset_1(X2,X2,X1,k6_partfun1(X2))
      | k6_partfun1(X2) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f78,f82])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f131,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f93,f120])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f129,plain,
    ( ~ spl4_3
    | spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f116,f108,f126,f118])).

fof(f116,plain,
    ( k1_relat_1(sK2) = k10_relat_1(sK2,sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f62,f110])).

fof(f114,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f113])).

fof(f113,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f55,f106])).

fof(f106,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f104])).

fof(f112,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f102,f108,f104])).

fof(f102,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f47,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:50:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (28250)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (28252)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (28258)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (28265)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (28269)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (28249)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (28260)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (28251)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (28253)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.54  % (28247)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.37/0.54  % (28255)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.54  % (28275)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.37/0.54  % (28276)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.37/0.55  % (28273)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.37/0.55  % (28274)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.37/0.55  % (28268)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (28257)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.55  % (28275)Refutation not found, incomplete strategy% (28275)------------------------------
% 1.37/0.55  % (28275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (28275)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (28275)Memory used [KB]: 11001
% 1.37/0.55  % (28275)Time elapsed: 0.143 s
% 1.37/0.55  % (28275)------------------------------
% 1.37/0.55  % (28275)------------------------------
% 1.37/0.55  % (28267)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.37/0.55  % (28248)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.37/0.55  % (28271)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.55  % (28259)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.37/0.56  % (28266)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.56  % (28261)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.37/0.56  % (28263)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.37/0.56  % (28263)Refutation not found, incomplete strategy% (28263)------------------------------
% 1.37/0.56  % (28263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (28263)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.56  
% 1.37/0.56  % (28263)Memory used [KB]: 10746
% 1.37/0.56  % (28263)Time elapsed: 0.159 s
% 1.37/0.56  % (28263)------------------------------
% 1.37/0.56  % (28263)------------------------------
% 1.58/0.57  % (28256)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.58/0.57  % (28272)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.58/0.58  % (28270)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.58  % (28264)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.58/0.58  % (28262)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.58/0.59  % (28260)Refutation found. Thanks to Tanya!
% 1.58/0.59  % SZS status Theorem for theBenchmark
% 1.58/0.59  % SZS output start Proof for theBenchmark
% 1.58/0.59  fof(f872,plain,(
% 1.58/0.59    $false),
% 1.58/0.59    inference(avatar_sat_refutation,[],[f112,f114,f129,f131,f155,f213,f215,f217,f231,f244,f297,f301,f322,f324,f332,f356,f416,f441,f483,f490,f515,f516,f527,f555,f569,f591,f594,f597,f607,f747,f794,f802,f826,f830,f834,f871])).
% 1.58/0.59  fof(f871,plain,(
% 1.58/0.59    ~spl4_20 | ~spl4_55),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f859])).
% 1.58/0.59  fof(f859,plain,(
% 1.58/0.59    $false | (~spl4_20 | ~spl4_55)),
% 1.58/0.59    inference(subsumption_resolution,[],[f52,f837])).
% 1.58/0.59  fof(f837,plain,(
% 1.58/0.59    sK3 = k2_funct_1(sK2) | (~spl4_20 | ~spl4_55)),
% 1.58/0.59    inference(forward_demodulation,[],[f574,f284])).
% 1.58/0.59  fof(f284,plain,(
% 1.58/0.59    sK2 = k2_funct_1(sK3) | ~spl4_20),
% 1.58/0.59    inference(avatar_component_clause,[],[f282])).
% 1.58/0.59  fof(f282,plain,(
% 1.58/0.59    spl4_20 <=> sK2 = k2_funct_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.58/0.59  fof(f574,plain,(
% 1.58/0.59    sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_55),
% 1.58/0.59    inference(avatar_component_clause,[],[f572])).
% 1.58/0.59  fof(f572,plain,(
% 1.58/0.59    spl4_55 <=> sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_55])])).
% 1.58/0.59  fof(f52,plain,(
% 1.58/0.59    sK3 != k2_funct_1(sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f21,plain,(
% 1.58/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.58/0.59    inference(flattening,[],[f20])).
% 1.58/0.59  fof(f20,plain,(
% 1.58/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.58/0.59    inference(ennf_transformation,[],[f19])).
% 1.58/0.59  fof(f19,negated_conjecture,(
% 1.58/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.58/0.59    inference(negated_conjecture,[],[f18])).
% 1.58/0.59  fof(f18,conjecture,(
% 1.58/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.58/0.59  fof(f834,plain,(
% 1.58/0.59    ~spl4_2 | ~spl4_20 | spl4_58),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f833])).
% 1.58/0.59  fof(f833,plain,(
% 1.58/0.59    $false | (~spl4_2 | ~spl4_20 | spl4_58)),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f832])).
% 1.58/0.59  fof(f832,plain,(
% 1.58/0.59    k6_partfun1(sK1) != k6_partfun1(sK1) | (~spl4_2 | ~spl4_20 | spl4_58)),
% 1.58/0.59    inference(forward_demodulation,[],[f831,f110])).
% 1.58/0.59  fof(f110,plain,(
% 1.58/0.59    sK1 = k2_relat_1(sK2) | ~spl4_2),
% 1.58/0.59    inference(avatar_component_clause,[],[f108])).
% 1.58/0.59  fof(f108,plain,(
% 1.58/0.59    spl4_2 <=> sK1 = k2_relat_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.58/0.59  fof(f831,plain,(
% 1.58/0.59    k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1) | (~spl4_20 | spl4_58)),
% 1.58/0.59    inference(forward_demodulation,[],[f586,f284])).
% 1.58/0.59  fof(f586,plain,(
% 1.58/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | spl4_58),
% 1.58/0.59    inference(avatar_component_clause,[],[f584])).
% 1.58/0.59  fof(f584,plain,(
% 1.58/0.59    spl4_58 <=> k6_partfun1(sK1) = k6_partfun1(k2_relat_1(k2_funct_1(sK3)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_58])])).
% 1.58/0.59  fof(f830,plain,(
% 1.58/0.59    ~spl4_20 | spl4_56),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f829])).
% 1.58/0.59  fof(f829,plain,(
% 1.58/0.59    $false | (~spl4_20 | spl4_56)),
% 1.58/0.59    inference(subsumption_resolution,[],[f49,f828])).
% 1.58/0.59  fof(f828,plain,(
% 1.58/0.59    ~v2_funct_1(sK2) | (~spl4_20 | spl4_56)),
% 1.58/0.59    inference(forward_demodulation,[],[f578,f284])).
% 1.58/0.59  fof(f578,plain,(
% 1.58/0.59    ~v2_funct_1(k2_funct_1(sK3)) | spl4_56),
% 1.58/0.59    inference(avatar_component_clause,[],[f576])).
% 1.58/0.59  fof(f576,plain,(
% 1.58/0.59    spl4_56 <=> v2_funct_1(k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_56])])).
% 1.58/0.59  fof(f49,plain,(
% 1.58/0.59    v2_funct_1(sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f826,plain,(
% 1.58/0.59    ~spl4_20 | ~spl4_36 | spl4_59),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f825])).
% 1.58/0.59  fof(f825,plain,(
% 1.58/0.59    $false | (~spl4_20 | ~spl4_36 | spl4_59)),
% 1.58/0.59    inference(subsumption_resolution,[],[f415,f810])).
% 1.58/0.59  fof(f810,plain,(
% 1.58/0.59    sK0 != k1_relat_1(sK2) | (~spl4_20 | spl4_59)),
% 1.58/0.59    inference(superposition,[],[f590,f284])).
% 1.58/0.59  fof(f590,plain,(
% 1.58/0.59    sK0 != k1_relat_1(k2_funct_1(sK3)) | spl4_59),
% 1.58/0.59    inference(avatar_component_clause,[],[f588])).
% 1.58/0.59  fof(f588,plain,(
% 1.58/0.59    spl4_59 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 1.58/0.59  fof(f415,plain,(
% 1.58/0.59    sK0 = k1_relat_1(sK2) | ~spl4_36),
% 1.58/0.59    inference(avatar_component_clause,[],[f413])).
% 1.58/0.59  fof(f413,plain,(
% 1.58/0.59    spl4_36 <=> sK0 = k1_relat_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.58/0.59  fof(f802,plain,(
% 1.58/0.59    spl4_85),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f799])).
% 1.58/0.59  fof(f799,plain,(
% 1.58/0.59    $false | spl4_85),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f83,f793])).
% 1.58/0.59  fof(f793,plain,(
% 1.58/0.59    ~v2_funct_1(k6_partfun1(sK0)) | spl4_85),
% 1.58/0.59    inference(avatar_component_clause,[],[f791])).
% 1.58/0.59  fof(f791,plain,(
% 1.58/0.59    spl4_85 <=> v2_funct_1(k6_partfun1(sK0))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 1.58/0.59  fof(f83,plain,(
% 1.58/0.59    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.58/0.59    inference(definition_unfolding,[],[f59,f56])).
% 1.58/0.59  fof(f56,plain,(
% 1.58/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f14])).
% 1.58/0.59  fof(f14,axiom,(
% 1.58/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.58/0.59  fof(f59,plain,(
% 1.58/0.59    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f5])).
% 1.58/0.59  fof(f5,axiom,(
% 1.58/0.59    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.58/0.59  fof(f794,plain,(
% 1.58/0.59    ~spl4_45 | ~spl4_9 | ~spl4_10 | spl4_49 | spl4_21 | ~spl4_85 | ~spl4_7 | ~spl4_60),
% 1.58/0.59    inference(avatar_split_clause,[],[f787,f605,f152,f791,f286,f507,f199,f195,f480])).
% 1.58/0.59  fof(f480,plain,(
% 1.58/0.59    spl4_45 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 1.58/0.59  fof(f195,plain,(
% 1.58/0.59    spl4_9 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.58/0.59  fof(f199,plain,(
% 1.58/0.59    spl4_10 <=> v1_funct_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.58/0.59  fof(f507,plain,(
% 1.58/0.59    spl4_49 <=> k1_xboole_0 = sK0),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.58/0.59  fof(f286,plain,(
% 1.58/0.59    spl4_21 <=> v2_funct_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.58/0.59  fof(f152,plain,(
% 1.58/0.59    spl4_7 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.58/0.59  fof(f605,plain,(
% 1.58/0.59    spl4_60 <=> ! [X1,X0] : (~v1_funct_1(X0) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 1.58/0.59  fof(f787,plain,(
% 1.58/0.59    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | (~spl4_7 | ~spl4_60)),
% 1.58/0.59    inference(superposition,[],[f606,f154])).
% 1.58/0.59  fof(f154,plain,(
% 1.58/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~spl4_7),
% 1.58/0.59    inference(avatar_component_clause,[],[f152])).
% 1.58/0.59  fof(f606,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | v2_funct_1(X0) | k1_xboole_0 = X1 | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v1_funct_2(X0,sK1,X1)) ) | ~spl4_60),
% 1.58/0.59    inference(avatar_component_clause,[],[f605])).
% 1.58/0.59  fof(f747,plain,(
% 1.58/0.59    spl4_57),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f745])).
% 1.58/0.59  fof(f745,plain,(
% 1.58/0.59    $false | spl4_57),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f92,f44,f582,f65])).
% 1.58/0.59  fof(f65,plain,(
% 1.58/0.59    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f25,plain,(
% 1.58/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.59    inference(flattening,[],[f24])).
% 1.58/0.59  fof(f24,plain,(
% 1.58/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f4])).
% 1.58/0.59  fof(f4,axiom,(
% 1.58/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.58/0.59  fof(f582,plain,(
% 1.58/0.59    ~v1_funct_1(k2_funct_1(sK3)) | spl4_57),
% 1.58/0.59    inference(avatar_component_clause,[],[f580])).
% 1.58/0.59  fof(f580,plain,(
% 1.58/0.59    spl4_57 <=> v1_funct_1(k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 1.58/0.59  fof(f44,plain,(
% 1.58/0.59    v1_funct_1(sK3)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f92,plain,(
% 1.58/0.59    v1_relat_1(sK3)),
% 1.58/0.59    inference(resolution,[],[f68,f46])).
% 1.58/0.59  fof(f46,plain,(
% 1.58/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f68,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f30])).
% 1.58/0.59  fof(f30,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.59    inference(ennf_transformation,[],[f8])).
% 1.58/0.59  fof(f8,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.58/0.59  fof(f607,plain,(
% 1.58/0.59    ~spl4_8 | spl4_60 | ~spl4_1 | ~spl4_27),
% 1.58/0.59    inference(avatar_split_clause,[],[f603,f319,f104,f605,f191])).
% 1.58/0.59  fof(f191,plain,(
% 1.58/0.59    spl4_8 <=> v1_funct_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.58/0.59  fof(f104,plain,(
% 1.58/0.59    spl4_1 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.58/0.59  fof(f319,plain,(
% 1.58/0.59    spl4_27 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 1.58/0.59  fof(f603,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f598])).
% 1.58/0.59  fof(f598,plain,(
% 1.58/0.59    ( ! [X0,X1] : (sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,X1))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X1,sK2,X0)) | ~v1_funct_1(sK2) | k1_xboole_0 = X1 | v2_funct_1(X0)) )),
% 1.58/0.59    inference(superposition,[],[f76,f47])).
% 1.58/0.59  fof(f47,plain,(
% 1.58/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f76,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~v1_funct_1(X3) | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f37])).
% 1.58/0.59  fof(f37,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.58/0.59    inference(flattening,[],[f36])).
% 1.58/0.59  fof(f36,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.58/0.59    inference(ennf_transformation,[],[f16])).
% 1.58/0.59  fof(f16,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.58/0.59  fof(f597,plain,(
% 1.58/0.59    spl4_22 | ~spl4_47),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f596])).
% 1.58/0.59  fof(f596,plain,(
% 1.58/0.59    $false | (spl4_22 | ~spl4_47)),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f595])).
% 1.58/0.59  fof(f595,plain,(
% 1.58/0.59    k6_partfun1(sK0) != k6_partfun1(sK0) | (spl4_22 | ~spl4_47)),
% 1.58/0.59    inference(forward_demodulation,[],[f292,f500])).
% 1.58/0.59  fof(f500,plain,(
% 1.58/0.59    sK0 = k2_relat_1(sK3) | ~spl4_47),
% 1.58/0.59    inference(avatar_component_clause,[],[f498])).
% 1.58/0.59  fof(f498,plain,(
% 1.58/0.59    spl4_47 <=> sK0 = k2_relat_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).
% 1.58/0.59  fof(f292,plain,(
% 1.58/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | spl4_22),
% 1.58/0.59    inference(avatar_component_clause,[],[f290])).
% 1.58/0.59  fof(f290,plain,(
% 1.58/0.59    spl4_22 <=> k6_partfun1(sK0) = k6_partfun1(k2_relat_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.58/0.59  fof(f594,plain,(
% 1.58/0.59    spl4_54),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f592])).
% 1.58/0.59  fof(f592,plain,(
% 1.58/0.59    $false | spl4_54),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f92,f44,f568,f64])).
% 1.58/0.59  fof(f64,plain,(
% 1.58/0.59    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f568,plain,(
% 1.58/0.59    ~v1_relat_1(k2_funct_1(sK3)) | spl4_54),
% 1.58/0.59    inference(avatar_component_clause,[],[f566])).
% 1.58/0.59  fof(f566,plain,(
% 1.58/0.59    spl4_54 <=> v1_relat_1(k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.58/0.59  fof(f591,plain,(
% 1.58/0.59    spl4_55 | ~spl4_54 | ~spl4_56 | ~spl4_10 | ~spl4_15 | ~spl4_57 | ~spl4_58 | ~spl4_59 | ~spl4_47 | ~spl4_50),
% 1.58/0.59    inference(avatar_split_clause,[],[f570,f512,f498,f588,f584,f580,f257,f199,f576,f566,f572])).
% 1.58/0.59  fof(f257,plain,(
% 1.58/0.59    spl4_15 <=> v1_relat_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.58/0.59  fof(f512,plain,(
% 1.58/0.59    spl4_50 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 1.58/0.59  fof(f570,plain,(
% 1.58/0.59    sK0 != k1_relat_1(k2_funct_1(sK3)) | k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | (~spl4_47 | ~spl4_50)),
% 1.58/0.59    inference(forward_demodulation,[],[f560,f500])).
% 1.58/0.59  fof(f560,plain,(
% 1.58/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(k2_funct_1(sK3))) | ~v1_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k2_funct_1(sK3)) | k2_relat_1(sK3) != k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~spl4_50),
% 1.58/0.59    inference(superposition,[],[f87,f514])).
% 1.58/0.59  fof(f514,plain,(
% 1.58/0.59    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_50),
% 1.58/0.59    inference(avatar_component_clause,[],[f512])).
% 1.58/0.59  fof(f87,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v1_relat_1(X0) | k2_funct_1(X0) = X1) )),
% 1.58/0.59    inference(definition_unfolding,[],[f66,f56])).
% 1.58/0.59  fof(f66,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 1.58/0.59    inference(cnf_transformation,[],[f27])).
% 1.58/0.59  fof(f27,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.59    inference(flattening,[],[f26])).
% 1.58/0.59  fof(f26,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f7])).
% 1.58/0.59  fof(f7,axiom,(
% 1.58/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.58/0.59  fof(f569,plain,(
% 1.58/0.59    ~spl4_54 | ~spl4_15 | ~spl4_21 | ~spl4_10 | spl4_23 | ~spl4_47 | ~spl4_50 | ~spl4_52),
% 1.58/0.59    inference(avatar_split_clause,[],[f564,f524,f512,f498,f294,f199,f286,f257,f566])).
% 1.58/0.59  fof(f294,plain,(
% 1.58/0.59    spl4_23 <=> sK1 = k1_relat_1(sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.58/0.59  fof(f524,plain,(
% 1.58/0.59    spl4_52 <=> k1_relat_1(sK3) = k10_relat_1(sK3,sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_52])])).
% 1.58/0.59  fof(f564,plain,(
% 1.58/0.59    sK1 = k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_47 | ~spl4_50 | ~spl4_52)),
% 1.58/0.59    inference(forward_demodulation,[],[f563,f526])).
% 1.58/0.59  fof(f526,plain,(
% 1.58/0.59    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | ~spl4_52),
% 1.58/0.59    inference(avatar_component_clause,[],[f524])).
% 1.58/0.59  fof(f563,plain,(
% 1.58/0.59    sK1 = k10_relat_1(sK3,sK0) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_47 | ~spl4_50)),
% 1.58/0.59    inference(forward_demodulation,[],[f562,f500])).
% 1.58/0.59  fof(f562,plain,(
% 1.58/0.59    sK1 = k10_relat_1(sK3,k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_50),
% 1.58/0.59    inference(forward_demodulation,[],[f561,f85])).
% 1.58/0.59  fof(f85,plain,(
% 1.58/0.59    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.58/0.59    inference(definition_unfolding,[],[f61,f56])).
% 1.58/0.59  fof(f61,plain,(
% 1.58/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.58/0.59    inference(cnf_transformation,[],[f3])).
% 1.58/0.59  fof(f3,axiom,(
% 1.58/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 1.58/0.59  fof(f561,plain,(
% 1.58/0.59    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~spl4_50),
% 1.58/0.59    inference(duplicate_literal_removal,[],[f559])).
% 1.58/0.59  fof(f559,plain,(
% 1.58/0.59    k10_relat_1(sK3,k2_relat_1(sK3)) = k2_relat_1(k6_partfun1(sK1)) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_50),
% 1.58/0.59    inference(superposition,[],[f136,f514])).
% 1.58/0.59  fof(f136,plain,(
% 1.58/0.59    ( ! [X2,X3] : (k2_relat_1(k5_relat_1(X3,k2_funct_1(X2))) = k10_relat_1(X2,k2_relat_1(X3)) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | ~v1_relat_1(X2) | ~v1_relat_1(k2_funct_1(X2)) | ~v1_relat_1(X3)) )),
% 1.58/0.59    inference(superposition,[],[f67,f63])).
% 1.58/0.59  fof(f63,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f23])).
% 1.58/0.59  fof(f23,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.58/0.59    inference(ennf_transformation,[],[f1])).
% 1.58/0.59  fof(f1,axiom,(
% 1.58/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).
% 1.58/0.59  fof(f67,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f29])).
% 1.58/0.59  fof(f29,plain,(
% 1.58/0.59    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.58/0.59    inference(flattening,[],[f28])).
% 1.58/0.59  fof(f28,plain,(
% 1.58/0.59    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.58/0.59    inference(ennf_transformation,[],[f6])).
% 1.58/0.59  fof(f6,axiom,(
% 1.58/0.59    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 1.58/0.59  fof(f555,plain,(
% 1.58/0.59    ~spl4_49),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f538])).
% 1.58/0.59  fof(f538,plain,(
% 1.58/0.59    $false | ~spl4_49),
% 1.58/0.59    inference(subsumption_resolution,[],[f50,f509])).
% 1.58/0.59  fof(f509,plain,(
% 1.58/0.59    k1_xboole_0 = sK0 | ~spl4_49),
% 1.58/0.59    inference(avatar_component_clause,[],[f507])).
% 1.58/0.59  fof(f50,plain,(
% 1.58/0.59    k1_xboole_0 != sK0),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f527,plain,(
% 1.58/0.59    ~spl4_15 | spl4_52 | ~spl4_47),
% 1.58/0.59    inference(avatar_split_clause,[],[f518,f498,f524,f257])).
% 1.58/0.59  fof(f518,plain,(
% 1.58/0.59    k1_relat_1(sK3) = k10_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_47),
% 1.58/0.59    inference(superposition,[],[f62,f500])).
% 1.58/0.59  fof(f62,plain,(
% 1.58/0.59    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f22])).
% 1.58/0.59  fof(f22,plain,(
% 1.58/0.59    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.58/0.59    inference(ennf_transformation,[],[f2])).
% 1.58/0.59  fof(f2,axiom,(
% 1.58/0.59    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.58/0.59  fof(f516,plain,(
% 1.58/0.59    ~spl4_9 | spl4_47 | ~spl4_44),
% 1.58/0.59    inference(avatar_split_clause,[],[f494,f476,f498,f195])).
% 1.58/0.59  fof(f476,plain,(
% 1.58/0.59    spl4_44 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 1.58/0.59  fof(f494,plain,(
% 1.58/0.59    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_44),
% 1.58/0.59    inference(superposition,[],[f69,f478])).
% 1.58/0.59  fof(f478,plain,(
% 1.58/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_44),
% 1.58/0.59    inference(avatar_component_clause,[],[f476])).
% 1.58/0.59  fof(f69,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f31])).
% 1.58/0.59  fof(f31,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.59    inference(ennf_transformation,[],[f9])).
% 1.58/0.59  fof(f9,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.58/0.59  fof(f515,plain,(
% 1.58/0.59    spl4_50 | spl4_49 | ~spl4_21 | ~spl4_10 | ~spl4_9 | ~spl4_45 | ~spl4_44),
% 1.58/0.59    inference(avatar_split_clause,[],[f495,f476,f480,f195,f199,f286,f507,f512])).
% 1.58/0.59  fof(f495,plain,(
% 1.58/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_44),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f493])).
% 1.58/0.59  fof(f493,plain,(
% 1.58/0.59    sK0 != sK0 | ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_44),
% 1.58/0.59    inference(superposition,[],[f70,f478])).
% 1.58/0.59  fof(f70,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f33])).
% 1.58/0.59  fof(f33,plain,(
% 1.58/0.59    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.58/0.59    inference(flattening,[],[f32])).
% 1.58/0.59  fof(f32,plain,(
% 1.58/0.59    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.58/0.59    inference(ennf_transformation,[],[f17])).
% 1.58/0.59  fof(f17,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.58/0.59  fof(f490,plain,(
% 1.58/0.59    spl4_45),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f489])).
% 1.58/0.59  fof(f489,plain,(
% 1.58/0.59    $false | spl4_45),
% 1.58/0.59    inference(subsumption_resolution,[],[f45,f482])).
% 1.58/0.59  fof(f482,plain,(
% 1.58/0.59    ~v1_funct_2(sK3,sK1,sK0) | spl4_45),
% 1.58/0.59    inference(avatar_component_clause,[],[f480])).
% 1.58/0.59  fof(f45,plain,(
% 1.58/0.59    v1_funct_2(sK3,sK1,sK0)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f483,plain,(
% 1.58/0.59    spl4_44 | ~spl4_10 | ~spl4_1 | ~spl4_27 | ~spl4_8 | ~spl4_9 | ~spl4_45),
% 1.58/0.59    inference(avatar_split_clause,[],[f471,f480,f195,f191,f319,f104,f199,f476])).
% 1.58/0.59  fof(f471,plain,(
% 1.58/0.59    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.58/0.59    inference(resolution,[],[f72,f48])).
% 1.58/0.59  fof(f48,plain,(
% 1.58/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f72,plain,(
% 1.58/0.59    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.58/0.59    inference(cnf_transformation,[],[f35])).
% 1.58/0.59  fof(f35,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.58/0.59    inference(flattening,[],[f34])).
% 1.58/0.59  fof(f34,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.58/0.59    inference(ennf_transformation,[],[f15])).
% 1.58/0.59  fof(f15,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.58/0.59  fof(f441,plain,(
% 1.58/0.59    spl4_32),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f439])).
% 1.58/0.59  fof(f439,plain,(
% 1.58/0.59    $false | spl4_32),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f93,f53,f392,f64])).
% 1.58/0.59  fof(f392,plain,(
% 1.58/0.59    ~v1_relat_1(k2_funct_1(sK2)) | spl4_32),
% 1.58/0.59    inference(avatar_component_clause,[],[f390])).
% 1.58/0.59  fof(f390,plain,(
% 1.58/0.59    spl4_32 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.58/0.59  fof(f53,plain,(
% 1.58/0.59    v1_funct_1(sK2)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f93,plain,(
% 1.58/0.59    v1_relat_1(sK2)),
% 1.58/0.59    inference(resolution,[],[f68,f55])).
% 1.58/0.59  fof(f55,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f416,plain,(
% 1.58/0.59    ~spl4_32 | ~spl4_3 | ~spl4_26 | ~spl4_8 | spl4_36 | ~spl4_2 | ~spl4_5 | ~spl4_24),
% 1.58/0.59    inference(avatar_split_clause,[],[f411,f307,f126,f108,f413,f191,f315,f118,f390])).
% 1.58/0.59  fof(f118,plain,(
% 1.58/0.59    spl4_3 <=> v1_relat_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.58/0.59  fof(f315,plain,(
% 1.58/0.59    spl4_26 <=> v2_funct_1(sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 1.58/0.59  fof(f126,plain,(
% 1.58/0.59    spl4_5 <=> k1_relat_1(sK2) = k10_relat_1(sK2,sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.58/0.59  fof(f307,plain,(
% 1.58/0.59    spl4_24 <=> k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.58/0.59  fof(f411,plain,(
% 1.58/0.59    sK0 = k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_5 | ~spl4_24)),
% 1.58/0.59    inference(forward_demodulation,[],[f410,f128])).
% 1.58/0.59  fof(f128,plain,(
% 1.58/0.59    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~spl4_5),
% 1.58/0.59    inference(avatar_component_clause,[],[f126])).
% 1.58/0.59  fof(f410,plain,(
% 1.58/0.59    sK0 = k10_relat_1(sK2,sK1) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_2 | ~spl4_24)),
% 1.58/0.59    inference(forward_demodulation,[],[f409,f110])).
% 1.58/0.59  fof(f409,plain,(
% 1.58/0.59    sK0 = k10_relat_1(sK2,k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 1.58/0.59    inference(forward_demodulation,[],[f388,f85])).
% 1.58/0.59  fof(f388,plain,(
% 1.58/0.59    k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl4_24),
% 1.58/0.59    inference(duplicate_literal_removal,[],[f386])).
% 1.58/0.59  fof(f386,plain,(
% 1.58/0.59    k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl4_24),
% 1.58/0.59    inference(superposition,[],[f136,f309])).
% 1.58/0.59  fof(f309,plain,(
% 1.58/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_24),
% 1.58/0.59    inference(avatar_component_clause,[],[f307])).
% 1.58/0.59  fof(f356,plain,(
% 1.58/0.59    ~spl4_25),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f342])).
% 1.58/0.59  fof(f342,plain,(
% 1.58/0.59    $false | ~spl4_25),
% 1.58/0.59    inference(subsumption_resolution,[],[f51,f313])).
% 1.58/0.59  fof(f313,plain,(
% 1.58/0.59    k1_xboole_0 = sK1 | ~spl4_25),
% 1.58/0.59    inference(avatar_component_clause,[],[f311])).
% 1.58/0.59  fof(f311,plain,(
% 1.58/0.59    spl4_25 <=> k1_xboole_0 = sK1),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.58/0.59  fof(f51,plain,(
% 1.58/0.59    k1_xboole_0 != sK1),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f332,plain,(
% 1.58/0.59    spl4_27),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f331])).
% 1.58/0.59  fof(f331,plain,(
% 1.58/0.59    $false | spl4_27),
% 1.58/0.59    inference(subsumption_resolution,[],[f54,f321])).
% 1.58/0.59  fof(f321,plain,(
% 1.58/0.59    ~v1_funct_2(sK2,sK0,sK1) | spl4_27),
% 1.58/0.59    inference(avatar_component_clause,[],[f319])).
% 1.58/0.59  fof(f54,plain,(
% 1.58/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f324,plain,(
% 1.58/0.59    spl4_26),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f323])).
% 1.58/0.59  fof(f323,plain,(
% 1.58/0.59    $false | spl4_26),
% 1.58/0.59    inference(subsumption_resolution,[],[f49,f317])).
% 1.58/0.59  fof(f317,plain,(
% 1.58/0.59    ~v2_funct_1(sK2) | spl4_26),
% 1.58/0.59    inference(avatar_component_clause,[],[f315])).
% 1.58/0.59  fof(f322,plain,(
% 1.58/0.59    spl4_24 | spl4_25 | ~spl4_26 | ~spl4_8 | ~spl4_1 | ~spl4_27),
% 1.58/0.59    inference(avatar_split_clause,[],[f305,f319,f104,f191,f315,f311,f307])).
% 1.58/0.59  fof(f305,plain,(
% 1.58/0.59    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.58/0.59    inference(trivial_inequality_removal,[],[f302])).
% 1.58/0.59  fof(f302,plain,(
% 1.58/0.59    sK1 != sK1 | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.58/0.59    inference(superposition,[],[f70,f47])).
% 1.58/0.59  fof(f301,plain,(
% 1.58/0.59    spl4_15),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f298])).
% 1.58/0.59  fof(f298,plain,(
% 1.58/0.59    $false | spl4_15),
% 1.58/0.59    inference(subsumption_resolution,[],[f92,f259])).
% 1.58/0.59  fof(f259,plain,(
% 1.58/0.59    ~v1_relat_1(sK3) | spl4_15),
% 1.58/0.59    inference(avatar_component_clause,[],[f257])).
% 1.58/0.59  fof(f297,plain,(
% 1.58/0.59    spl4_20 | ~spl4_15 | ~spl4_21 | ~spl4_8 | ~spl4_3 | ~spl4_10 | ~spl4_22 | ~spl4_23 | ~spl4_2 | ~spl4_13),
% 1.58/0.59    inference(avatar_split_clause,[],[f280,f234,f108,f294,f290,f199,f118,f191,f286,f257,f282])).
% 1.58/0.59  fof(f234,plain,(
% 1.58/0.59    spl4_13 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.58/0.59  fof(f280,plain,(
% 1.58/0.59    sK1 != k1_relat_1(sK3) | k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_2 | ~spl4_13)),
% 1.58/0.59    inference(forward_demodulation,[],[f255,f110])).
% 1.58/0.59  fof(f255,plain,(
% 1.58/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~spl4_13),
% 1.58/0.59    inference(superposition,[],[f87,f236])).
% 1.58/0.59  fof(f236,plain,(
% 1.58/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_13),
% 1.58/0.59    inference(avatar_component_clause,[],[f234])).
% 1.58/0.59  fof(f244,plain,(
% 1.58/0.59    ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_1 | spl4_13 | ~spl4_7),
% 1.58/0.59    inference(avatar_split_clause,[],[f241,f152,f234,f104,f199,f195,f191])).
% 1.58/0.59  fof(f241,plain,(
% 1.58/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~spl4_7),
% 1.58/0.59    inference(superposition,[],[f79,f154])).
% 1.58/0.59  fof(f79,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f41])).
% 1.58/0.59  fof(f41,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.58/0.59    inference(flattening,[],[f40])).
% 1.58/0.59  fof(f40,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.58/0.59    inference(ennf_transformation,[],[f13])).
% 1.58/0.59  fof(f13,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.58/0.59  fof(f231,plain,(
% 1.58/0.59    spl4_6),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f222])).
% 1.58/0.59  fof(f222,plain,(
% 1.58/0.59    $false | spl4_6),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f53,f44,f46,f55,f150,f81])).
% 1.58/0.59  fof(f81,plain,(
% 1.58/0.59    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f43])).
% 1.58/0.59  fof(f43,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.58/0.59    inference(flattening,[],[f42])).
% 1.58/0.59  fof(f42,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.58/0.59    inference(ennf_transformation,[],[f12])).
% 1.58/0.59  fof(f12,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.58/0.59  fof(f150,plain,(
% 1.58/0.59    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_6),
% 1.58/0.59    inference(avatar_component_clause,[],[f148])).
% 1.58/0.59  fof(f148,plain,(
% 1.58/0.59    spl4_6 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.58/0.59  fof(f217,plain,(
% 1.58/0.59    spl4_10),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f216])).
% 1.58/0.59  fof(f216,plain,(
% 1.58/0.59    $false | spl4_10),
% 1.58/0.59    inference(subsumption_resolution,[],[f44,f201])).
% 1.58/0.59  fof(f201,plain,(
% 1.58/0.59    ~v1_funct_1(sK3) | spl4_10),
% 1.58/0.59    inference(avatar_component_clause,[],[f199])).
% 1.58/0.59  fof(f215,plain,(
% 1.58/0.59    spl4_9),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f214])).
% 1.58/0.59  fof(f214,plain,(
% 1.58/0.59    $false | spl4_9),
% 1.58/0.59    inference(subsumption_resolution,[],[f46,f197])).
% 1.58/0.59  fof(f197,plain,(
% 1.58/0.59    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_9),
% 1.58/0.59    inference(avatar_component_clause,[],[f195])).
% 1.58/0.59  fof(f213,plain,(
% 1.58/0.59    spl4_8),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f212])).
% 1.58/0.59  fof(f212,plain,(
% 1.58/0.59    $false | spl4_8),
% 1.58/0.59    inference(subsumption_resolution,[],[f53,f193])).
% 1.58/0.59  fof(f193,plain,(
% 1.58/0.59    ~v1_funct_1(sK2) | spl4_8),
% 1.58/0.59    inference(avatar_component_clause,[],[f191])).
% 1.58/0.59  fof(f155,plain,(
% 1.58/0.59    ~spl4_6 | spl4_7),
% 1.58/0.59    inference(avatar_split_clause,[],[f145,f152,f148])).
% 1.58/0.59  fof(f145,plain,(
% 1.58/0.59    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.58/0.59    inference(resolution,[],[f139,f48])).
% 1.58/0.59  fof(f139,plain,(
% 1.58/0.59    ( ! [X2,X1] : (~r2_relset_1(X2,X2,X1,k6_partfun1(X2)) | k6_partfun1(X2) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.58/0.59    inference(resolution,[],[f78,f82])).
% 1.58/0.59  fof(f82,plain,(
% 1.58/0.59    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.58/0.59    inference(definition_unfolding,[],[f57,f56])).
% 1.58/0.59  fof(f57,plain,(
% 1.58/0.59    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f11])).
% 1.58/0.59  fof(f11,axiom,(
% 1.58/0.59    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.58/0.59  fof(f78,plain,(
% 1.58/0.59    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f39])).
% 1.58/0.59  fof(f39,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.58/0.59    inference(flattening,[],[f38])).
% 1.58/0.59  fof(f38,plain,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.58/0.59    inference(ennf_transformation,[],[f10])).
% 1.58/0.59  fof(f10,axiom,(
% 1.58/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.58/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.58/0.59  fof(f131,plain,(
% 1.58/0.59    spl4_3),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f130])).
% 1.58/0.59  fof(f130,plain,(
% 1.58/0.59    $false | spl4_3),
% 1.58/0.59    inference(subsumption_resolution,[],[f93,f120])).
% 1.58/0.59  fof(f120,plain,(
% 1.58/0.59    ~v1_relat_1(sK2) | spl4_3),
% 1.58/0.59    inference(avatar_component_clause,[],[f118])).
% 1.58/0.59  fof(f129,plain,(
% 1.58/0.59    ~spl4_3 | spl4_5 | ~spl4_2),
% 1.58/0.59    inference(avatar_split_clause,[],[f116,f108,f126,f118])).
% 1.58/0.59  fof(f116,plain,(
% 1.58/0.59    k1_relat_1(sK2) = k10_relat_1(sK2,sK1) | ~v1_relat_1(sK2) | ~spl4_2),
% 1.58/0.59    inference(superposition,[],[f62,f110])).
% 1.58/0.59  fof(f114,plain,(
% 1.58/0.59    spl4_1),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f113])).
% 1.58/0.59  fof(f113,plain,(
% 1.58/0.59    $false | spl4_1),
% 1.58/0.59    inference(subsumption_resolution,[],[f55,f106])).
% 1.58/0.59  fof(f106,plain,(
% 1.58/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_1),
% 1.58/0.59    inference(avatar_component_clause,[],[f104])).
% 1.58/0.59  fof(f112,plain,(
% 1.58/0.59    ~spl4_1 | spl4_2),
% 1.58/0.59    inference(avatar_split_clause,[],[f102,f108,f104])).
% 1.58/0.59  fof(f102,plain,(
% 1.58/0.59    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.58/0.59    inference(superposition,[],[f47,f69])).
% 1.58/0.59  % SZS output end Proof for theBenchmark
% 1.58/0.59  % (28260)------------------------------
% 1.58/0.59  % (28260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (28260)Termination reason: Refutation
% 1.58/0.59  
% 1.58/0.59  % (28260)Memory used [KB]: 7164
% 1.58/0.59  % (28260)Time elapsed: 0.191 s
% 1.58/0.59  % (28260)------------------------------
% 1.58/0.59  % (28260)------------------------------
% 1.58/0.59  % (28246)Success in time 0.227 s
%------------------------------------------------------------------------------
