%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  163 ( 587 expanded)
%              Number of leaves         :   21 ( 118 expanded)
%              Depth                    :   29
%              Number of atoms          :  661 (4202 expanded)
%              Number of equality atoms :  176 (1373 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f350,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f179,f182,f223,f268,f279,f349])).

fof(f349,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f347,f46])).

fof(f46,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f347,plain,
    ( sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f346,f38])).

fof(f38,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f346,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f345,f173])).

fof(f173,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl4_4
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f345,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f344,f126])).

fof(f126,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f100,f125])).

fof(f125,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f124,f38])).

fof(f124,plain,
    ( ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f123,f49])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f48,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f122,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f121,f47])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f120,f40])).

fof(f40,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f118,f39])).

fof(f39,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f118,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f42,f65])).

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
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f42,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f344,plain,
    ( sK0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(superposition,[],[f160,f329])).

fof(f329,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f178,f326])).

fof(f326,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f325,f47])).

fof(f325,plain,
    ( ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f324,f148])).

fof(f148,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f324,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f323,f113])).

fof(f113,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f108,f41])).

fof(f41,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f49,f70])).

fof(f323,plain,
    ( sK1 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f321])).

fof(f321,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(superposition,[],[f285,f222])).

fof(f222,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl4_7
  <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f285,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,sK3)
        | k2_relat_1(X2) != sK1
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k2_funct_1(sK3) = X2 )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f284,f169])).

fof(f169,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl4_3
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f284,plain,
    ( ! [X2] :
        ( k6_partfun1(sK0) != k5_relat_1(X2,sK3)
        | k2_relat_1(X2) != sK1
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(sK3)
        | k2_funct_1(sK3) = X2 )
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f134,f173])).

fof(f134,plain,(
    ! [X2] :
      ( k6_partfun1(sK0) != k5_relat_1(X2,sK3)
      | k2_relat_1(X2) != sK1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k2_funct_1(sK3) = X2 ) ),
    inference(forward_demodulation,[],[f133,f126])).

fof(f133,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK1
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X2,sK3)
      | k2_funct_1(sK3) = X2 ) ),
    inference(subsumption_resolution,[],[f130,f38])).

fof(f130,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK1
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(sK3)
      | ~ v1_relat_1(sK3)
      | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X2,sK3)
      | k2_funct_1(sK3) = X2 ) ),
    inference(superposition,[],[f74,f103])).

fof(f103,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f99,f95])).

fof(f95,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f93,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f93,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f39,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f99,plain,(
    k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f40,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f178,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_5
  <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f160,plain,
    ( ! [X2] :
        ( k6_partfun1(sK1) != k5_relat_1(X2,sK2)
        | k2_relat_1(X2) != sK0
        | ~ v1_relat_1(X2)
        | ~ v1_funct_1(X2)
        | k2_funct_1(sK2) = X2 )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f141,f148])).

fof(f141,plain,(
    ! [X2] :
      ( k6_partfun1(sK1) != k5_relat_1(X2,sK2)
      | k2_relat_1(X2) != sK0
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k2_funct_1(sK2) = X2 ) ),
    inference(forward_demodulation,[],[f140,f113])).

fof(f140,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(sK2)
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2 ) ),
    inference(subsumption_resolution,[],[f139,f43])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2 ) ),
    inference(subsumption_resolution,[],[f137,f47])).

fof(f137,plain,(
    ! [X2] :
      ( k2_relat_1(X2) != sK0
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ v2_funct_1(sK2)
      | ~ v1_relat_1(sK2)
      | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2)
      | k2_funct_1(sK2) = X2 ) ),
    inference(superposition,[],[f74,f111])).

fof(f111,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f107,f98])).

fof(f98,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f97,f49])).

fof(f97,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f96,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f96,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f48,f58])).

fof(f107,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f49,f73])).

fof(f279,plain,
    ( ~ spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f277,f77])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f277,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f195,f222])).

fof(f195,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f194,f47])).

fof(f194,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | ~ spl4_1
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f193,f148])).

fof(f193,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_3
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f191])).

fof(f191,plain,
    ( sK1 != sK1
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | spl4_3
    | ~ spl4_4 ),
    inference(superposition,[],[f184,f113])).

fof(f184,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK1
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK3)) )
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f183,f173])).

fof(f183,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK1
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK3))
        | ~ v1_relat_1(sK3) )
    | spl4_3 ),
    inference(subsumption_resolution,[],[f132,f170])).

fof(f170,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f168])).

fof(f132,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_relat_1(sK3)
      | v2_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f129,f38])).

fof(f129,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK1
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,sK3))
      | ~ v1_relat_1(sK3)
      | v2_funct_1(sK3) ) ),
    inference(superposition,[],[f60,f103])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f268,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f267])).

fof(f267,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f266,f47])).

fof(f266,plain,
    ( ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f265,f40])).

fof(f265,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f264,f38])).

fof(f264,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f263,f49])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f258,f218])).

fof(f218,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl4_6
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f258,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f68,f210])).

fof(f210,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f207,f47])).

fof(f207,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f106,f49])).

fof(f106,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(subsumption_resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X3)
      | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3) ) ),
    inference(resolution,[],[f40,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_1(X4)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f223,plain,
    ( ~ spl4_6
    | spl4_7 ),
    inference(avatar_split_clause,[],[f213,f220,f216])).

fof(f213,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f211,f210])).

fof(f211,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f119,f210])).

fof(f119,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f117,f79])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f72,f66])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f117,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f42,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f182,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f181])).

fof(f181,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f40,f180])).

fof(f180,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_4 ),
    inference(resolution,[],[f174,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f174,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f179,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f104,f176,f172,f168])).

fof(f104,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f87,f103])).

fof(f87,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(resolution,[],[f38,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f157,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f49,f155])).

fof(f155,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl4_1 ),
    inference(resolution,[],[f149,f71])).

fof(f149,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f147])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:51:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (11349)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (11341)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (11332)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11328)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (11329)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (11338)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (11337)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (11355)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (11327)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (11326)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (11352)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (11347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.54  % (11340)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (11353)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (11330)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (11354)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (11351)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (11350)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (11343)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (11342)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (11343)Refutation not found, incomplete strategy% (11343)------------------------------
% 0.21/0.55  % (11343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11343)Memory used [KB]: 10746
% 0.21/0.55  % (11343)Time elapsed: 0.139 s
% 0.21/0.55  % (11343)------------------------------
% 0.21/0.55  % (11343)------------------------------
% 0.21/0.55  % (11344)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (11345)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (11334)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (11346)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (11333)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.56  % (11335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (11355)Refutation not found, incomplete strategy% (11355)------------------------------
% 0.21/0.56  % (11355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11355)Memory used [KB]: 11001
% 0.21/0.56  % (11355)Time elapsed: 0.146 s
% 0.21/0.56  % (11355)------------------------------
% 0.21/0.56  % (11355)------------------------------
% 0.21/0.56  % (11336)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (11336)Refutation not found, incomplete strategy% (11336)------------------------------
% 0.21/0.56  % (11336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (11336)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (11336)Memory used [KB]: 11001
% 0.21/0.56  % (11336)Time elapsed: 0.153 s
% 0.21/0.56  % (11336)------------------------------
% 0.21/0.56  % (11336)------------------------------
% 0.21/0.57  % (11354)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f350,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f157,f179,f182,f223,f268,f279,f349])).
% 0.21/0.57  fof(f349,plain,(
% 0.21/0.57    ~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f348])).
% 0.21/0.57  fof(f348,plain,(
% 0.21/0.57    $false | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f347,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    sK3 != k2_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f16])).
% 0.21/0.57  fof(f16,negated_conjecture,(
% 0.21/0.57    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f15])).
% 0.21/0.57  fof(f15,conjecture,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.21/0.57  fof(f347,plain,(
% 0.21/0.57    sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f346,f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    v1_funct_1(sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f346,plain,(
% 0.21/0.57    ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f345,f173])).
% 0.21/0.57  fof(f173,plain,(
% 0.21/0.57    v1_relat_1(sK3) | ~spl4_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f172])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    spl4_4 <=> v1_relat_1(sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.57  fof(f345,plain,(
% 0.21/0.57    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f344,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    sK0 = k2_relat_1(sK3)),
% 0.21/0.57    inference(backward_demodulation,[],[f100,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f124,f38])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f123,f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f122,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f121,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    v1_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f120,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f118,f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    v1_funct_2(sK3,sK1,sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ~v1_funct_2(sK3,sK1,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(resolution,[],[f42,f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.57    inference(flattening,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    k2_relat_1(sK3) = k2_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(resolution,[],[f40,f70])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    sK0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f343])).
% 0.21/0.57  fof(f343,plain,(
% 0.21/0.57    k6_partfun1(sK1) != k6_partfun1(sK1) | sK0 != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(superposition,[],[f160,f329])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f178,f326])).
% 0.21/0.57  fof(f326,plain,(
% 0.21/0.57    sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f325,f47])).
% 0.21/0.57  fof(f325,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f324,f148])).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    v1_relat_1(sK2) | ~spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    spl4_1 <=> v1_relat_1(sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f324,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f323,f113])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    sK1 = k2_relat_1(sK2)),
% 0.21/0.57    inference(forward_demodulation,[],[f108,f41])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.21/0.57    inference(resolution,[],[f49,f70])).
% 0.21/0.57  fof(f323,plain,(
% 0.21/0.57    sK1 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f321])).
% 0.21/0.57  fof(f321,plain,(
% 0.21/0.57    k6_partfun1(sK0) != k6_partfun1(sK0) | sK1 != k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(superposition,[],[f285,f222])).
% 0.21/0.57  fof(f222,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f220])).
% 0.21/0.57  fof(f220,plain,(
% 0.21/0.57    spl4_7 <=> k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.57  fof(f285,plain,(
% 0.21/0.57    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,sK3) | k2_relat_1(X2) != sK1 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k2_funct_1(sK3) = X2) ) | (~spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f284,f169])).
% 0.21/0.57  fof(f169,plain,(
% 0.21/0.57    v2_funct_1(sK3) | ~spl4_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f168])).
% 0.21/0.57  fof(f168,plain,(
% 0.21/0.57    spl4_3 <=> v2_funct_1(sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.57  fof(f284,plain,(
% 0.21/0.57    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,sK3) | k2_relat_1(X2) != sK1 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK3) | k2_funct_1(sK3) = X2) ) | ~spl4_4),
% 0.21/0.57    inference(subsumption_resolution,[],[f134,f173])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X2] : (k6_partfun1(sK0) != k5_relat_1(X2,sK3) | k2_relat_1(X2) != sK1 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | k2_funct_1(sK3) = X2) )),
% 0.21/0.57    inference(forward_demodulation,[],[f133,f126])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X2,sK3) | k2_funct_1(sK3) = X2) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f130,f38])).
% 0.21/0.57  fof(f130,plain,(
% 0.21/0.57    ( ! [X2] : (k2_relat_1(X2) != sK1 | ~v1_funct_1(sK3) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X2,sK3) | k2_funct_1(sK3) = X2) )),
% 0.21/0.57    inference(superposition,[],[f74,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    sK1 = k1_relat_1(sK3)),
% 0.21/0.57    inference(forward_demodulation,[],[f99,f95])).
% 0.21/0.57  fof(f95,plain,(
% 0.21/0.57    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.57  fof(f94,plain,(
% 0.21/0.57    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f93,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    k1_xboole_0 != sK0),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.57    inference(resolution,[],[f39,f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    k1_relat_1(sK3) = k1_relset_1(sK1,sK0,sK3)),
% 0.21/0.57    inference(resolution,[],[f40,f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f37])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | ~v1_relat_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.21/0.57    inference(definition_unfolding,[],[f50,f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,axiom,(
% 0.21/0.57    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_funct_1(X0) = X1) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.21/0.57  fof(f178,plain,(
% 0.21/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~spl4_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f176])).
% 0.21/0.57  fof(f176,plain,(
% 0.21/0.57    spl4_5 <=> k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ( ! [X2] : (k6_partfun1(sK1) != k5_relat_1(X2,sK2) | k2_relat_1(X2) != sK0 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | k2_funct_1(sK2) = X2) ) | ~spl4_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f141,f148])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ( ! [X2] : (k6_partfun1(sK1) != k5_relat_1(X2,sK2) | k2_relat_1(X2) != sK0 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k2_funct_1(sK2) = X2) )),
% 0.21/0.57    inference(forward_demodulation,[],[f140,f113])).
% 0.21/0.57  fof(f140,plain,(
% 0.21/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v1_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f139,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    v2_funct_1(sK2)),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f137,f47])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    ( ! [X2] : (k2_relat_1(X2) != sK0 | ~v1_funct_1(sK2) | ~v1_relat_1(X2) | ~v1_funct_1(X2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | k6_partfun1(k2_relat_1(sK2)) != k5_relat_1(X2,sK2) | k2_funct_1(sK2) = X2) )),
% 0.21/0.57    inference(superposition,[],[f74,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    sK0 = k1_relat_1(sK2)),
% 0.21/0.57    inference(forward_demodulation,[],[f107,f98])).
% 0.21/0.57  fof(f98,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    inference(subsumption_resolution,[],[f97,f49])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f96,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    k1_xboole_0 != sK1),
% 0.21/0.57    inference(cnf_transformation,[],[f18])).
% 0.21/0.57  fof(f96,plain,(
% 0.21/0.57    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.57    inference(resolution,[],[f48,f58])).
% 0.21/0.57  fof(f107,plain,(
% 0.21/0.57    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 0.21/0.57    inference(resolution,[],[f49,f73])).
% 0.21/0.57  fof(f279,plain,(
% 0.21/0.57    ~spl4_1 | spl4_3 | ~spl4_4 | ~spl4_7),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.57  fof(f278,plain,(
% 0.21/0.57    $false | (~spl4_1 | spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(subsumption_resolution,[],[f277,f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f62,f66])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    ~v2_funct_1(k6_partfun1(sK0)) | (~spl4_1 | spl4_3 | ~spl4_4 | ~spl4_7)),
% 0.21/0.57    inference(backward_demodulation,[],[f195,f222])).
% 0.21/0.57  fof(f195,plain,(
% 0.21/0.57    ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_1 | spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f194,f47])).
% 0.21/0.57  fof(f194,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (~spl4_1 | spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f193,f148])).
% 0.21/0.57  fof(f193,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(trivial_inequality_removal,[],[f191])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    sK1 != sK1 | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,sK3)) | (spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(superposition,[],[f184,f113])).
% 0.21/0.57  fof(f184,plain,(
% 0.21/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3))) ) | (spl4_3 | ~spl4_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f183,f173])).
% 0.21/0.57  fof(f183,plain,(
% 0.21/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_relat_1(sK3)) ) | spl4_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f132,f170])).
% 0.21/0.57  fof(f170,plain,(
% 0.21/0.57    ~v2_funct_1(sK3) | spl4_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f168])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_relat_1(sK3) | v2_funct_1(sK3)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f129,f38])).
% 0.21/0.57  fof(f129,plain,(
% 0.21/0.57    ( ! [X1] : (k2_relat_1(X1) != sK1 | ~v1_funct_1(sK3) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK3)) | ~v1_relat_1(sK3) | v2_funct_1(sK3)) )),
% 0.21/0.57    inference(superposition,[],[f60,f103])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_relat_1(X0) | v2_funct_1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 0.21/0.57  fof(f268,plain,(
% 0.21/0.57    spl4_6),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f267])).
% 0.21/0.57  fof(f267,plain,(
% 0.21/0.57    $false | spl4_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f266,f47])).
% 0.21/0.57  fof(f266,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | spl4_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f265,f40])).
% 0.21/0.57  fof(f265,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f264,f38])).
% 0.21/0.57  fof(f264,plain,(
% 0.21/0.57    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f263,f49])).
% 0.21/0.57  fof(f263,plain,(
% 0.21/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | spl4_6),
% 0.21/0.57    inference(subsumption_resolution,[],[f258,f218])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_6),
% 0.21/0.57    inference(avatar_component_clause,[],[f216])).
% 0.21/0.57  fof(f216,plain,(
% 0.21/0.57    spl4_6 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.57  fof(f258,plain,(
% 0.21/0.57    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2)),
% 0.21/0.57    inference(superposition,[],[f68,f210])).
% 0.21/0.57  fof(f210,plain,(
% 0.21/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.21/0.57    inference(subsumption_resolution,[],[f207,f47])).
% 0.21/0.57  fof(f207,plain,(
% 0.21/0.57    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.21/0.57    inference(resolution,[],[f106,f49])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f102,f38])).
% 0.21/0.57  fof(f102,plain,(
% 0.21/0.57    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_1(sK3) | ~v1_funct_1(X3) | k1_partfun1(X4,X5,sK1,sK0,X3,sK3) = k5_relat_1(X3,sK3)) )),
% 0.21/0.57    inference(resolution,[],[f40,f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~v1_funct_1(X4) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f12])).
% 0.21/0.57  fof(f12,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.57    inference(flattening,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.21/0.57  fof(f223,plain,(
% 0.21/0.57    ~spl4_6 | spl4_7),
% 0.21/0.57    inference(avatar_split_clause,[],[f213,f220,f216])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(forward_demodulation,[],[f211,f210])).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 0.21/0.57    inference(backward_demodulation,[],[f119,f210])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(subsumption_resolution,[],[f117,f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f72,f66])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f9])).
% 0.21/0.57  fof(f9,axiom,(
% 0.21/0.57    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.21/0.57    inference(resolution,[],[f42,f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(flattening,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.21/0.57    inference(ennf_transformation,[],[f8])).
% 0.21/0.57  fof(f8,axiom,(
% 0.21/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.21/0.57  fof(f182,plain,(
% 0.21/0.57    spl4_4),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f181])).
% 0.21/0.57  fof(f181,plain,(
% 0.21/0.57    $false | spl4_4),
% 0.21/0.57    inference(subsumption_resolution,[],[f40,f180])).
% 0.21/0.57  fof(f180,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_4),
% 0.21/0.57    inference(resolution,[],[f174,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    ~v1_relat_1(sK3) | spl4_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f172])).
% 0.21/0.57  fof(f179,plain,(
% 0.21/0.57    ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f104,f176,f172,f168])).
% 0.21/0.57  fof(f104,plain,(
% 0.21/0.57    k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) | ~v1_relat_1(sK3) | ~v2_funct_1(sK3)),
% 0.21/0.57    inference(backward_demodulation,[],[f87,f103])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ~v1_relat_1(sK3) | ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))),
% 0.21/0.57    inference(resolution,[],[f38,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))) )),
% 0.21/0.57    inference(definition_unfolding,[],[f51,f66])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.57    inference(flattening,[],[f21])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    spl4_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f156])).
% 0.21/0.57  fof(f156,plain,(
% 0.21/0.57    $false | spl4_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f49,f155])).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl4_1),
% 0.21/0.57    inference(resolution,[],[f149,f71])).
% 0.21/0.57  fof(f149,plain,(
% 0.21/0.57    ~v1_relat_1(sK2) | spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f147])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (11354)------------------------------
% 0.21/0.57  % (11354)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (11354)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (11354)Memory used [KB]: 6396
% 0.21/0.57  % (11354)Time elapsed: 0.161 s
% 0.21/0.57  % (11354)------------------------------
% 0.21/0.57  % (11354)------------------------------
% 0.21/0.57  % (11324)Success in time 0.205 s
%------------------------------------------------------------------------------
