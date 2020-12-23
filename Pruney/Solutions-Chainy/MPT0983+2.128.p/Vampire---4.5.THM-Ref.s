%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:53 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 310 expanded)
%              Number of leaves         :   46 ( 108 expanded)
%              Depth                    :    9
%              Number of atoms          :  544 (1193 expanded)
%              Number of equality atoms :   89 ( 107 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f845,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f109,f139,f157,f166,f175,f179,f290,f292,f325,f327,f370,f386,f405,f508,f510,f512,f518,f527,f537,f550,f554,f573,f579,f801,f844])).

fof(f844,plain,
    ( ~ spl4_5
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f842])).

fof(f842,plain,
    ( $false
    | ~ spl4_5
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f56,f134,f612,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ v1_xboole_0(X0)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f612,plain,
    ( k1_xboole_0 != sK2
    | spl4_42 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl4_42
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f134,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_5
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f801,plain,
    ( spl4_2
    | ~ spl4_42 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | spl4_2
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f110,f774])).

fof(f774,plain,
    ( ~ v2_funct_1(k1_xboole_0)
    | spl4_2
    | ~ spl4_42 ),
    inference(superposition,[],[f108,f613])).

fof(f613,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f611])).

fof(f108,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f110,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f88,f87])).

fof(f87,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f57,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f57,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f58,f59])).

fof(f58,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f579,plain,
    ( spl4_2
    | ~ spl4_9
    | ~ spl4_33
    | ~ spl4_7
    | ~ spl4_32
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(avatar_split_clause,[],[f578,f515,f321,f492,f150,f496,f159,f106])).

fof(f159,plain,
    ( spl4_9
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f496,plain,
    ( spl4_33
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f150,plain,
    ( spl4_7
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f492,plain,
    ( spl4_32
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f321,plain,
    ( spl4_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f515,plain,
    ( spl4_36
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f578,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(trivial_inequality_removal,[],[f577])).

fof(f577,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl4_24
    | ~ spl4_36 ),
    inference(forward_demodulation,[],[f576,f323])).

fof(f323,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f321])).

fof(f576,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | v2_funct_1(sK2)
    | ~ spl4_36 ),
    inference(superposition,[],[f90,f517])).

fof(f517,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f515])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f573,plain,(
    spl4_34 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl4_34 ),
    inference(unit_resulting_resolution,[],[f55,f51,f502,f459])).

fof(f459,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f456])).

fof(f456,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f86,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

fof(f502,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f500])).

fof(f500,plain,
    ( spl4_34
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f51,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f55,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f554,plain,(
    spl4_40 ),
    inference(avatar_contradiction_clause,[],[f551])).

fof(f551,plain,
    ( $false
    | spl4_40 ),
    inference(subsumption_resolution,[],[f181,f549])).

fof(f549,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | spl4_40 ),
    inference(avatar_component_clause,[],[f547])).

fof(f547,plain,
    ( spl4_40
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f181,plain,(
    v5_relat_1(sK3,sK0) ),
    inference(resolution,[],[f74,f51])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f550,plain,
    ( spl4_1
    | ~ spl4_7
    | ~ spl4_40
    | ~ spl4_38 ),
    inference(avatar_split_clause,[],[f540,f533,f547,f150,f102])).

fof(f102,plain,
    ( spl4_1
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f533,plain,
    ( spl4_38
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f540,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | v2_funct_2(sK3,sK0)
    | ~ spl4_38 ),
    inference(superposition,[],[f91,f535])).

fof(f535,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_38 ),
    inference(avatar_component_clause,[],[f533])).

fof(f91,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f537,plain,
    ( ~ spl4_21
    | spl4_38
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f531,f524,f533,f298])).

fof(f298,plain,
    ( spl4_21
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f524,plain,
    ( spl4_37
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f531,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_37 ),
    inference(superposition,[],[f72,f526])).

fof(f526,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f524])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f527,plain,
    ( spl4_37
    | ~ spl4_33
    | ~ spl4_23
    | ~ spl4_18
    | ~ spl4_32
    | ~ spl4_21
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f519,f264,f298,f492,f277,f317,f496,f524])).

fof(f317,plain,
    ( spl4_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f277,plain,
    ( spl4_18
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f264,plain,
    ( spl4_15
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f519,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f81,f52])).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f518,plain,
    ( ~ spl4_34
    | spl4_36
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f513,f505,f515,f500])).

fof(f505,plain,
    ( spl4_35
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f513,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_35 ),
    inference(resolution,[],[f507,f309])).

fof(f309,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X3,X3,X2,k6_partfun1(X3))
      | k6_partfun1(X3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f83,f89])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f507,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f505])).

fof(f512,plain,(
    spl4_33 ),
    inference(avatar_contradiction_clause,[],[f511])).

fof(f511,plain,
    ( $false
    | spl4_33 ),
    inference(subsumption_resolution,[],[f49,f498])).

fof(f498,plain,
    ( ~ v1_funct_1(sK3)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f496])).

fof(f49,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f510,plain,(
    spl4_32 ),
    inference(avatar_contradiction_clause,[],[f509])).

fof(f509,plain,
    ( $false
    | spl4_32 ),
    inference(subsumption_resolution,[],[f53,f494])).

fof(f494,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_32 ),
    inference(avatar_component_clause,[],[f492])).

fof(f53,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f508,plain,
    ( ~ spl4_32
    | ~ spl4_21
    | ~ spl4_33
    | ~ spl4_23
    | spl4_35 ),
    inference(avatar_split_clause,[],[f490,f505,f317,f496,f298,f492])).

fof(f490,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f52,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f405,plain,
    ( ~ spl4_18
    | spl4_19
    | spl4_20 ),
    inference(avatar_split_clause,[],[f399,f285,f281,f277])).

fof(f281,plain,
    ( spl4_19
  <=> sK0 = k1_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f285,plain,
    ( spl4_20
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f399,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f55,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f386,plain,
    ( spl4_6
    | ~ spl4_20 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl4_6
    | ~ spl4_20 ),
    inference(subsumption_resolution,[],[f56,f382])).

fof(f382,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl4_6
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f375,f92])).

fof(f92,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f375,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0))
    | spl4_6
    | ~ spl4_20 ),
    inference(superposition,[],[f138,f287])).

fof(f287,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f285])).

fof(f138,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl4_6
  <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f370,plain,(
    spl4_23 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | spl4_23 ),
    inference(subsumption_resolution,[],[f55,f319])).

fof(f319,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f317])).

fof(f327,plain,(
    spl4_21 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl4_21 ),
    inference(subsumption_resolution,[],[f51,f300])).

fof(f300,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl4_21 ),
    inference(avatar_component_clause,[],[f298])).

fof(f325,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f314,f281,f321,f317])).

fof(f314,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_19 ),
    inference(superposition,[],[f71,f283])).

fof(f283,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f281])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f292,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f54,f279])).

fof(f279,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f277])).

fof(f54,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f290,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f50,f266])).

fof(f266,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | spl4_15 ),
    inference(avatar_component_clause,[],[f264])).

fof(f50,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f179,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f176])).

fof(f176,plain,
    ( $false
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f64,f165])).

fof(f165,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl4_10
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f175,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f64,f156])).

fof(f156,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_8
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f166,plain,
    ( spl4_9
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f146,f163,f159])).

fof(f146,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f55])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f157,plain,
    ( spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f145,f154,f150])).

fof(f145,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f51])).

fof(f139,plain,
    ( spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f120,f136,f132])).

fof(f120,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f61,f55])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f109,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f48,f106,f102])).

fof(f48,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v2_funct_2(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.51  % (25081)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (25089)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.51  % (25066)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (25073)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (25068)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (25071)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (25067)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.52  % (25072)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (25079)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (25067)Refutation not found, incomplete strategy% (25067)------------------------------
% 0.20/0.52  % (25067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25067)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (25067)Memory used [KB]: 1791
% 0.20/0.52  % (25067)Time elapsed: 0.097 s
% 0.20/0.52  % (25067)------------------------------
% 0.20/0.52  % (25067)------------------------------
% 0.20/0.53  % (25074)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (25088)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (25095)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (25082)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (25080)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (25087)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (25090)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (25091)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (25070)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % (25075)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (25069)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.54  % (25082)Refutation not found, incomplete strategy% (25082)------------------------------
% 1.34/0.54  % (25082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (25082)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (25082)Memory used [KB]: 10746
% 1.34/0.54  % (25082)Time elapsed: 0.129 s
% 1.34/0.54  % (25082)------------------------------
% 1.34/0.54  % (25082)------------------------------
% 1.34/0.54  % (25094)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (25084)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.55  % (25077)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.55  % (25095)Refutation not found, incomplete strategy% (25095)------------------------------
% 1.34/0.55  % (25095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (25095)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (25095)Memory used [KB]: 1663
% 1.34/0.55  % (25095)Time elapsed: 0.003 s
% 1.34/0.55  % (25095)------------------------------
% 1.34/0.55  % (25095)------------------------------
% 1.34/0.55  % (25080)Refutation not found, incomplete strategy% (25080)------------------------------
% 1.34/0.55  % (25080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (25080)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (25080)Memory used [KB]: 1918
% 1.34/0.55  % (25080)Time elapsed: 0.134 s
% 1.34/0.55  % (25080)------------------------------
% 1.34/0.55  % (25080)------------------------------
% 1.34/0.55  % (25093)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.55  % (25086)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.55  % (25083)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.55  % (25085)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.56  % (25078)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.51/0.56  % (25076)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.51/0.56  % (25092)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (25079)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f845,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f109,f139,f157,f166,f175,f179,f290,f292,f325,f327,f370,f386,f405,f508,f510,f512,f518,f527,f537,f550,f554,f573,f579,f801,f844])).
% 1.51/0.56  fof(f844,plain,(
% 1.51/0.56    ~spl4_5 | spl4_42),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f842])).
% 1.51/0.56  fof(f842,plain,(
% 1.51/0.56    $false | (~spl4_5 | spl4_42)),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f56,f134,f612,f70])).
% 1.51/0.56  fof(f70,plain,(
% 1.51/0.56    ( ! [X0,X1] : (X0 = X1 | ~v1_xboole_0(X0) | ~v1_xboole_0(X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f32])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 1.51/0.56  fof(f612,plain,(
% 1.51/0.56    k1_xboole_0 != sK2 | spl4_42),
% 1.51/0.56    inference(avatar_component_clause,[],[f611])).
% 1.51/0.56  fof(f611,plain,(
% 1.51/0.56    spl4_42 <=> k1_xboole_0 = sK2),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.51/0.56  fof(f134,plain,(
% 1.51/0.56    v1_xboole_0(sK2) | ~spl4_5),
% 1.51/0.56    inference(avatar_component_clause,[],[f132])).
% 1.51/0.56  fof(f132,plain,(
% 1.51/0.56    spl4_5 <=> v1_xboole_0(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.51/0.56  fof(f56,plain,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    inference(cnf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    v1_xboole_0(k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.51/0.56  fof(f801,plain,(
% 1.51/0.56    spl4_2 | ~spl4_42),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f800])).
% 1.51/0.56  fof(f800,plain,(
% 1.51/0.56    $false | (spl4_2 | ~spl4_42)),
% 1.51/0.56    inference(subsumption_resolution,[],[f110,f774])).
% 1.51/0.56  fof(f774,plain,(
% 1.51/0.56    ~v2_funct_1(k1_xboole_0) | (spl4_2 | ~spl4_42)),
% 1.51/0.56    inference(superposition,[],[f108,f613])).
% 1.51/0.56  fof(f613,plain,(
% 1.51/0.56    k1_xboole_0 = sK2 | ~spl4_42),
% 1.51/0.56    inference(avatar_component_clause,[],[f611])).
% 1.51/0.56  fof(f108,plain,(
% 1.51/0.56    ~v2_funct_1(sK2) | spl4_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f106])).
% 1.51/0.56  fof(f106,plain,(
% 1.51/0.56    spl4_2 <=> v2_funct_1(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.51/0.56  fof(f110,plain,(
% 1.51/0.56    v2_funct_1(k1_xboole_0)),
% 1.51/0.56    inference(superposition,[],[f88,f87])).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 1.51/0.56    inference(definition_unfolding,[],[f57,f59])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f20])).
% 1.51/0.56  fof(f20,axiom,(
% 1.51/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.51/0.56    inference(cnf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,axiom,(
% 1.51/0.56    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.51/0.56  fof(f88,plain,(
% 1.51/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.51/0.56    inference(definition_unfolding,[],[f58,f59])).
% 1.51/0.56  fof(f58,plain,(
% 1.51/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f8])).
% 1.51/0.56  fof(f8,axiom,(
% 1.51/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.51/0.56  fof(f579,plain,(
% 1.51/0.56    spl4_2 | ~spl4_9 | ~spl4_33 | ~spl4_7 | ~spl4_32 | ~spl4_24 | ~spl4_36),
% 1.51/0.56    inference(avatar_split_clause,[],[f578,f515,f321,f492,f150,f496,f159,f106])).
% 1.51/0.56  fof(f159,plain,(
% 1.51/0.56    spl4_9 <=> v1_relat_1(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.51/0.56  fof(f496,plain,(
% 1.51/0.56    spl4_33 <=> v1_funct_1(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 1.51/0.56  fof(f150,plain,(
% 1.51/0.56    spl4_7 <=> v1_relat_1(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.51/0.56  fof(f492,plain,(
% 1.51/0.56    spl4_32 <=> v1_funct_1(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 1.51/0.56  fof(f321,plain,(
% 1.51/0.56    spl4_24 <=> sK0 = k1_relat_1(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 1.51/0.56  fof(f515,plain,(
% 1.51/0.56    spl4_36 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).
% 1.51/0.56  fof(f578,plain,(
% 1.51/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | v2_funct_1(sK2) | (~spl4_24 | ~spl4_36)),
% 1.51/0.56    inference(trivial_inequality_removal,[],[f577])).
% 1.51/0.56  fof(f577,plain,(
% 1.51/0.56    k6_partfun1(sK0) != k6_partfun1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | v2_funct_1(sK2) | (~spl4_24 | ~spl4_36)),
% 1.51/0.56    inference(forward_demodulation,[],[f576,f323])).
% 1.51/0.56  fof(f323,plain,(
% 1.51/0.56    sK0 = k1_relat_1(sK2) | ~spl4_24),
% 1.51/0.56    inference(avatar_component_clause,[],[f321])).
% 1.51/0.56  fof(f576,plain,(
% 1.51/0.56    k6_partfun1(sK0) != k6_partfun1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK2) | v2_funct_1(sK2) | ~spl4_36),
% 1.51/0.56    inference(superposition,[],[f90,f517])).
% 1.51/0.56  fof(f517,plain,(
% 1.51/0.56    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_36),
% 1.51/0.56    inference(avatar_component_clause,[],[f515])).
% 1.51/0.56  fof(f90,plain,(
% 1.51/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.51/0.56    inference(definition_unfolding,[],[f63,f59])).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f29])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.51/0.56    inference(flattening,[],[f28])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f9])).
% 1.51/0.56  fof(f9,axiom,(
% 1.51/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 1.51/0.56  fof(f573,plain,(
% 1.51/0.56    spl4_34),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f571])).
% 1.51/0.56  fof(f571,plain,(
% 1.51/0.56    $false | spl4_34),
% 1.51/0.56    inference(unit_resulting_resolution,[],[f55,f51,f502,f459])).
% 1.51/0.56  fof(f459,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f456])).
% 1.51/0.56  fof(f456,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(superposition,[],[f86,f85])).
% 1.51/0.56  fof(f85,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f45])).
% 1.51/0.56  fof(f45,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(flattening,[],[f44])).
% 1.51/0.56  fof(f44,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.51/0.56    inference(ennf_transformation,[],[f14])).
% 1.51/0.56  fof(f14,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).
% 1.51/0.56  fof(f86,plain,(
% 1.51/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f47])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(flattening,[],[f46])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.51/0.56    inference(ennf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).
% 1.51/0.56  fof(f502,plain,(
% 1.51/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_34),
% 1.51/0.56    inference(avatar_component_clause,[],[f500])).
% 1.51/0.56  fof(f500,plain,(
% 1.51/0.56    spl4_34 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.51/0.56    inference(flattening,[],[f24])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.51/0.56    inference(ennf_transformation,[],[f23])).
% 1.51/0.56  fof(f23,negated_conjecture,(
% 1.51/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.51/0.56    inference(negated_conjecture,[],[f22])).
% 1.51/0.56  fof(f22,conjecture,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f554,plain,(
% 1.51/0.56    spl4_40),
% 1.51/0.56    inference(avatar_contradiction_clause,[],[f551])).
% 1.51/0.56  fof(f551,plain,(
% 1.51/0.56    $false | spl4_40),
% 1.51/0.56    inference(subsumption_resolution,[],[f181,f549])).
% 1.51/0.56  fof(f549,plain,(
% 1.51/0.56    ~v5_relat_1(sK3,sK0) | spl4_40),
% 1.51/0.56    inference(avatar_component_clause,[],[f547])).
% 1.51/0.56  fof(f547,plain,(
% 1.51/0.56    spl4_40 <=> v5_relat_1(sK3,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 1.51/0.56  fof(f181,plain,(
% 1.51/0.56    v5_relat_1(sK3,sK0)),
% 1.51/0.56    inference(resolution,[],[f74,f51])).
% 1.51/0.56  fof(f74,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f35])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f10])).
% 1.51/0.56  fof(f10,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.51/0.56  fof(f550,plain,(
% 1.51/0.56    spl4_1 | ~spl4_7 | ~spl4_40 | ~spl4_38),
% 1.51/0.56    inference(avatar_split_clause,[],[f540,f533,f547,f150,f102])).
% 1.51/0.56  fof(f102,plain,(
% 1.51/0.56    spl4_1 <=> v2_funct_2(sK3,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.51/0.56  fof(f533,plain,(
% 1.51/0.56    spl4_38 <=> sK0 = k2_relat_1(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 1.51/0.56  fof(f540,plain,(
% 1.51/0.56    ~v5_relat_1(sK3,sK0) | ~v1_relat_1(sK3) | v2_funct_2(sK3,sK0) | ~spl4_38),
% 1.51/0.56    inference(superposition,[],[f91,f535])).
% 1.51/0.56  fof(f535,plain,(
% 1.51/0.56    sK0 = k2_relat_1(sK3) | ~spl4_38),
% 1.51/0.56    inference(avatar_component_clause,[],[f533])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1) | v2_funct_2(X1,k2_relat_1(X1))) )),
% 1.51/0.56    inference(equality_resolution,[],[f65])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | k2_relat_1(X1) != X0 | v2_funct_2(X1,X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f31])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.51/0.56    inference(flattening,[],[f30])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f18])).
% 1.51/0.56  fof(f18,axiom,(
% 1.51/0.56    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.51/0.56  fof(f537,plain,(
% 1.51/0.56    ~spl4_21 | spl4_38 | ~spl4_37),
% 1.51/0.56    inference(avatar_split_clause,[],[f531,f524,f533,f298])).
% 1.51/0.56  fof(f298,plain,(
% 1.51/0.56    spl4_21 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.51/0.56  fof(f524,plain,(
% 1.51/0.56    spl4_37 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.51/0.56  fof(f531,plain,(
% 1.51/0.56    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_37),
% 1.51/0.56    inference(superposition,[],[f72,f526])).
% 1.51/0.56  fof(f526,plain,(
% 1.51/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_37),
% 1.51/0.56    inference(avatar_component_clause,[],[f524])).
% 1.51/0.56  fof(f72,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.56    inference(cnf_transformation,[],[f34])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.56    inference(ennf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.51/0.56  fof(f527,plain,(
% 1.51/0.56    spl4_37 | ~spl4_33 | ~spl4_23 | ~spl4_18 | ~spl4_32 | ~spl4_21 | ~spl4_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f519,f264,f298,f492,f277,f317,f496,f524])).
% 1.51/0.56  fof(f317,plain,(
% 1.51/0.56    spl4_23 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.51/0.56  fof(f277,plain,(
% 1.51/0.56    spl4_18 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.51/0.56  fof(f264,plain,(
% 1.51/0.56    spl4_15 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 1.51/0.56  fof(f519,plain,(
% 1.51/0.56    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.51/0.56    inference(resolution,[],[f81,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 1.51/0.56    inference(cnf_transformation,[],[f39])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.51/0.56    inference(flattening,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.51/0.57    inference(ennf_transformation,[],[f21])).
% 1.51/0.57  fof(f21,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.51/0.57  fof(f518,plain,(
% 1.51/0.57    ~spl4_34 | spl4_36 | ~spl4_35),
% 1.51/0.57    inference(avatar_split_clause,[],[f513,f505,f515,f500])).
% 1.51/0.57  fof(f505,plain,(
% 1.51/0.57    spl4_35 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.51/0.57  fof(f513,plain,(
% 1.51/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_35),
% 1.51/0.57    inference(resolution,[],[f507,f309])).
% 1.51/0.57  fof(f309,plain,(
% 1.51/0.57    ( ! [X2,X3] : (~r2_relset_1(X3,X3,X2,k6_partfun1(X3)) | k6_partfun1(X3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 1.51/0.57    inference(resolution,[],[f83,f89])).
% 1.51/0.57  fof(f89,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.51/0.57    inference(definition_unfolding,[],[f60,f59])).
% 1.51/0.57  fof(f60,plain,(
% 1.51/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f16])).
% 1.51/0.57  fof(f16,axiom,(
% 1.51/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.51/0.57  fof(f83,plain,(
% 1.51/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f41])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(flattening,[],[f40])).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.51/0.57    inference(ennf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.51/0.57  fof(f507,plain,(
% 1.51/0.57    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~spl4_35),
% 1.51/0.57    inference(avatar_component_clause,[],[f505])).
% 1.51/0.57  fof(f512,plain,(
% 1.51/0.57    spl4_33),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f511])).
% 1.51/0.57  fof(f511,plain,(
% 1.51/0.57    $false | spl4_33),
% 1.51/0.57    inference(subsumption_resolution,[],[f49,f498])).
% 1.51/0.57  fof(f498,plain,(
% 1.51/0.57    ~v1_funct_1(sK3) | spl4_33),
% 1.51/0.57    inference(avatar_component_clause,[],[f496])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    v1_funct_1(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f510,plain,(
% 1.51/0.57    spl4_32),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f509])).
% 1.51/0.57  fof(f509,plain,(
% 1.51/0.57    $false | spl4_32),
% 1.51/0.57    inference(subsumption_resolution,[],[f53,f494])).
% 1.51/0.57  fof(f494,plain,(
% 1.51/0.57    ~v1_funct_1(sK2) | spl4_32),
% 1.51/0.57    inference(avatar_component_clause,[],[f492])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    v1_funct_1(sK2)),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f508,plain,(
% 1.51/0.57    ~spl4_32 | ~spl4_21 | ~spl4_33 | ~spl4_23 | spl4_35),
% 1.51/0.57    inference(avatar_split_clause,[],[f490,f505,f317,f496,f298,f492])).
% 1.51/0.57  fof(f490,plain,(
% 1.51/0.57    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 1.51/0.57    inference(superposition,[],[f52,f84])).
% 1.51/0.57  fof(f84,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f43])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.51/0.57    inference(flattening,[],[f42])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.51/0.57    inference(ennf_transformation,[],[f19])).
% 1.51/0.57  fof(f19,axiom,(
% 1.51/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.51/0.57  fof(f405,plain,(
% 1.51/0.57    ~spl4_18 | spl4_19 | spl4_20),
% 1.51/0.57    inference(avatar_split_clause,[],[f399,f285,f281,f277])).
% 1.51/0.57  fof(f281,plain,(
% 1.51/0.57    spl4_19 <=> sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.51/0.57  fof(f285,plain,(
% 1.51/0.57    spl4_20 <=> k1_xboole_0 = sK1),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.51/0.57  fof(f399,plain,(
% 1.51/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.51/0.57    inference(resolution,[],[f55,f80])).
% 1.51/0.57  fof(f80,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(flattening,[],[f36])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 1.51/0.57  fof(f386,plain,(
% 1.51/0.57    spl4_6 | ~spl4_20),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f385])).
% 1.51/0.57  fof(f385,plain,(
% 1.51/0.57    $false | (spl4_6 | ~spl4_20)),
% 1.51/0.57    inference(subsumption_resolution,[],[f56,f382])).
% 1.51/0.57  fof(f382,plain,(
% 1.51/0.57    ~v1_xboole_0(k1_xboole_0) | (spl4_6 | ~spl4_20)),
% 1.51/0.57    inference(forward_demodulation,[],[f375,f92])).
% 1.51/0.57  fof(f92,plain,(
% 1.51/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.51/0.57    inference(equality_resolution,[],[f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.51/0.57  fof(f375,plain,(
% 1.51/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,k1_xboole_0)) | (spl4_6 | ~spl4_20)),
% 1.51/0.57    inference(superposition,[],[f138,f287])).
% 1.51/0.57  fof(f287,plain,(
% 1.51/0.57    k1_xboole_0 = sK1 | ~spl4_20),
% 1.51/0.57    inference(avatar_component_clause,[],[f285])).
% 1.51/0.57  fof(f138,plain,(
% 1.51/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | spl4_6),
% 1.51/0.57    inference(avatar_component_clause,[],[f136])).
% 1.51/0.57  fof(f136,plain,(
% 1.51/0.57    spl4_6 <=> v1_xboole_0(k2_zfmisc_1(sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.51/0.57  fof(f370,plain,(
% 1.51/0.57    spl4_23),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f369])).
% 1.51/0.57  fof(f369,plain,(
% 1.51/0.57    $false | spl4_23),
% 1.51/0.57    inference(subsumption_resolution,[],[f55,f319])).
% 1.51/0.57  fof(f319,plain,(
% 1.51/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | spl4_23),
% 1.51/0.57    inference(avatar_component_clause,[],[f317])).
% 1.51/0.57  fof(f327,plain,(
% 1.51/0.57    spl4_21),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f326])).
% 1.51/0.57  fof(f326,plain,(
% 1.51/0.57    $false | spl4_21),
% 1.51/0.57    inference(subsumption_resolution,[],[f51,f300])).
% 1.51/0.57  fof(f300,plain,(
% 1.51/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl4_21),
% 1.51/0.57    inference(avatar_component_clause,[],[f298])).
% 1.51/0.57  fof(f325,plain,(
% 1.51/0.57    ~spl4_23 | spl4_24 | ~spl4_19),
% 1.51/0.57    inference(avatar_split_clause,[],[f314,f281,f321,f317])).
% 1.51/0.57  fof(f314,plain,(
% 1.51/0.57    sK0 = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_19),
% 1.51/0.57    inference(superposition,[],[f71,f283])).
% 1.51/0.57  fof(f283,plain,(
% 1.51/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~spl4_19),
% 1.51/0.57    inference(avatar_component_clause,[],[f281])).
% 1.51/0.57  fof(f71,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f33])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.51/0.57    inference(ennf_transformation,[],[f12])).
% 1.51/0.57  fof(f12,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.51/0.57  fof(f292,plain,(
% 1.51/0.57    spl4_18),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f291])).
% 1.51/0.57  fof(f291,plain,(
% 1.51/0.57    $false | spl4_18),
% 1.51/0.57    inference(subsumption_resolution,[],[f54,f279])).
% 1.51/0.57  fof(f279,plain,(
% 1.51/0.57    ~v1_funct_2(sK2,sK0,sK1) | spl4_18),
% 1.51/0.57    inference(avatar_component_clause,[],[f277])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    v1_funct_2(sK2,sK0,sK1)),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f290,plain,(
% 1.51/0.57    spl4_15),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f289])).
% 1.51/0.57  fof(f289,plain,(
% 1.51/0.57    $false | spl4_15),
% 1.51/0.57    inference(subsumption_resolution,[],[f50,f266])).
% 1.51/0.57  fof(f266,plain,(
% 1.51/0.57    ~v1_funct_2(sK3,sK1,sK0) | spl4_15),
% 1.51/0.57    inference(avatar_component_clause,[],[f264])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    v1_funct_2(sK3,sK1,sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f179,plain,(
% 1.51/0.57    spl4_10),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f176])).
% 1.51/0.57  fof(f176,plain,(
% 1.51/0.57    $false | spl4_10),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f64,f165])).
% 1.51/0.57  fof(f165,plain,(
% 1.51/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_10),
% 1.51/0.57    inference(avatar_component_clause,[],[f163])).
% 1.51/0.57  fof(f163,plain,(
% 1.51/0.57    spl4_10 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.51/0.57  fof(f64,plain,(
% 1.51/0.57    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.51/0.57    inference(cnf_transformation,[],[f6])).
% 1.51/0.57  fof(f6,axiom,(
% 1.51/0.57    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.51/0.57  fof(f175,plain,(
% 1.51/0.57    spl4_8),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f172])).
% 1.51/0.57  fof(f172,plain,(
% 1.51/0.57    $false | spl4_8),
% 1.51/0.57    inference(unit_resulting_resolution,[],[f64,f156])).
% 1.51/0.57  fof(f156,plain,(
% 1.51/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_8),
% 1.51/0.57    inference(avatar_component_clause,[],[f154])).
% 1.51/0.57  fof(f154,plain,(
% 1.51/0.57    spl4_8 <=> v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.51/0.57  fof(f166,plain,(
% 1.51/0.57    spl4_9 | ~spl4_10),
% 1.51/0.57    inference(avatar_split_clause,[],[f146,f163,f159])).
% 1.51/0.57  fof(f146,plain,(
% 1.51/0.57    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | v1_relat_1(sK2)),
% 1.51/0.57    inference(resolution,[],[f62,f55])).
% 1.51/0.57  fof(f62,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.51/0.57  fof(f157,plain,(
% 1.51/0.57    spl4_7 | ~spl4_8),
% 1.51/0.57    inference(avatar_split_clause,[],[f145,f154,f150])).
% 1.51/0.57  fof(f145,plain,(
% 1.51/0.57    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | v1_relat_1(sK3)),
% 1.51/0.57    inference(resolution,[],[f62,f51])).
% 1.51/0.57  fof(f139,plain,(
% 1.51/0.57    spl4_5 | ~spl4_6),
% 1.51/0.57    inference(avatar_split_clause,[],[f120,f136,f132])).
% 1.51/0.57  fof(f120,plain,(
% 1.51/0.57    ~v1_xboole_0(k2_zfmisc_1(sK0,sK1)) | v1_xboole_0(sK2)),
% 1.51/0.57    inference(resolution,[],[f61,f55])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f26])).
% 1.51/0.57  fof(f26,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.51/0.57    inference(ennf_transformation,[],[f4])).
% 1.51/0.57  fof(f4,axiom,(
% 1.51/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.51/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.51/0.57  fof(f109,plain,(
% 1.51/0.57    ~spl4_1 | ~spl4_2),
% 1.51/0.57    inference(avatar_split_clause,[],[f48,f106,f102])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ~v2_funct_1(sK2) | ~v2_funct_2(sK3,sK0)),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  % SZS output end Proof for theBenchmark
% 1.51/0.57  % (25079)------------------------------
% 1.51/0.57  % (25079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (25079)Termination reason: Refutation
% 1.51/0.57  
% 1.51/0.57  % (25079)Memory used [KB]: 6652
% 1.51/0.57  % (25079)Time elapsed: 0.151 s
% 1.51/0.57  % (25079)------------------------------
% 1.51/0.57  % (25079)------------------------------
% 1.51/0.57  % (25065)Success in time 0.198 s
%------------------------------------------------------------------------------
