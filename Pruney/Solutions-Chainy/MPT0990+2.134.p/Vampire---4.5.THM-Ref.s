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
% DateTime   : Thu Dec  3 13:02:52 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  231 (1324 expanded)
%              Number of leaves         :   31 ( 426 expanded)
%              Depth                    :   26
%              Number of atoms          :  965 (13050 expanded)
%              Number of equality atoms :  250 (4419 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f191,f195,f207,f334,f364,f368,f382,f443,f448,f487,f522])).

fof(f522,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(avatar_contradiction_clause,[],[f521])).

fof(f521,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f520,f442])).

fof(f442,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f440])).

fof(f440,plain,
    ( spl4_10
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f520,plain,
    ( sK0 != k1_relat_1(sK2)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f519,f176])).

fof(f176,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f117,f153])).

fof(f153,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f152,f57])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f48,f47])).

fof(f47,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

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

fof(f152,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f151,f58])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f151,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f150,f59])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f150,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f149,f54])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f149,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f148,f55])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f148,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f146,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f146,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f61,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f49])).

fof(f117,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f519,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(trivial_inequality_removal,[],[f518])).

fof(f518,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f517,f143])).

fof(f143,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f112,f60])).

fof(f60,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f112,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f56,f85])).

fof(f517,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f516,f185])).

fof(f185,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f516,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f515,f54])).

fof(f515,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f514,f358])).

fof(f358,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f357])).

fof(f357,plain,
    ( spl4_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f514,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f513,f57])).

fof(f513,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f512,f62])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f512,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f510,f65])).

fof(f65,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f49])).

fof(f510,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(superposition,[],[f97,f491])).

fof(f491,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK2)
    | ~ spl4_3
    | ~ spl4_7 ),
    inference(backward_demodulation,[],[f202,f377])).

fof(f377,plain,
    ( sK2 = k2_funct_1(sK3)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl4_7
  <=> sK2 = k2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f202,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f200])).

fof(f200,plain,
    ( spl4_3
  <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f81])).

fof(f81,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f487,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(avatar_contradiction_clause,[],[f486])).

fof(f486,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f485,f358])).

fof(f485,plain,
    ( ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f483,f57])).

fof(f483,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(resolution,[],[f479,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f479,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_8 ),
    inference(subsumption_resolution,[],[f478,f381])).

fof(f381,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f379])).

fof(f379,plain,
    ( spl4_8
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f478,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f477,f370])).

fof(f370,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f351,f358])).

fof(f351,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f348,f57])).

fof(f348,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f205,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f205,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl4_4
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f477,plain,
    ( sK1 = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f476,f99])).

fof(f99,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f87,f81])).

fof(f87,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f476,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f475,f202])).

fof(f475,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f470,f106])).

fof(f106,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f470,plain,
    ( ~ r1_tarski(sK0,sK0)
    | k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(superposition,[],[f449,f363])).

fof(f363,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl4_6
  <=> sK0 = k1_relat_1(k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f449,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f177,f358])).

fof(f177,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),sK0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0))
      | ~ v1_relat_1(sK3)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f91,f176])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0)
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).

fof(f448,plain,
    ( ~ spl4_1
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f447])).

fof(f447,plain,
    ( $false
    | ~ spl4_1
    | spl4_9 ),
    inference(subsumption_resolution,[],[f446,f185])).

fof(f446,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(subsumption_resolution,[],[f444,f54])).

fof(f444,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_9 ),
    inference(resolution,[],[f438,f71])).

fof(f438,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl4_9
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f443,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f433,f188,f184,f440,f436])).

fof(f188,plain,
    ( spl4_2
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f433,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f432,f197])).

fof(f197,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f111,f185])).

fof(f111,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f109,f54])).

fof(f109,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f70])).

fof(f432,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f431,f99])).

fof(f431,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f430,f137])).

fof(f137,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f136,f54])).

fof(f136,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f135,f55])).

fof(f135,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f134,f56])).

fof(f134,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f133,f62])).

fof(f133,plain,
    ( ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f127,f64])).

fof(f64,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f127,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f66,f60])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f430,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f427,f106])).

fof(f427,plain,
    ( ~ r1_tarski(sK1,sK1)
    | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(superposition,[],[f383,f190])).

fof(f190,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f188])).

fof(f383,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK1)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK2,X0))
        | ~ v1_relat_1(X0) )
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f144,f185])).

fof(f144,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_relat_1(X0),sK1)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK2,X0))
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f91,f143])).

fof(f382,plain,
    ( spl4_7
    | ~ spl4_8
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f372,f357,f204,f184,f379,f375])).

fof(f372,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f371,f358])).

fof(f371,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f345,f205])).

fof(f345,plain,
    ( sK1 != k1_relat_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f344,f143])).

fof(f344,plain,
    ( sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f343])).

fof(f343,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f342,f176])).

fof(f342,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f341,f57])).

fof(f341,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f340,f185])).

fof(f340,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f256,f54])).

fof(f256,plain,
    ( k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3))
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f97,f252])).

fof(f252,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f249,f251])).

fof(f251,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f250,f101])).

fof(f101,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f89,f81])).

fof(f89,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f250,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f238,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f238,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f61,f214])).

fof(f214,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f211,f57])).

fof(f211,plain,
    ( ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f115,f59])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f113,f54])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f56,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f249,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f248,f54])).

fof(f248,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f247,f56])).

fof(f247,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f246,f57])).

fof(f246,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f241,f59])).

fof(f241,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f83,f214])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f368,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | spl4_5 ),
    inference(subsumption_resolution,[],[f366,f90])).

fof(f90,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f366,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | spl4_5 ),
    inference(resolution,[],[f365,f59])).

fof(f365,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_5 ),
    inference(resolution,[],[f359,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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

fof(f359,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f357])).

fof(f364,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f350,f204,f361,f357])).

fof(f350,plain,
    ( sK0 = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f349,f176])).

fof(f349,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f347,f57])).

fof(f347,plain,
    ( k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(resolution,[],[f205,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f334,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f332,f98])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f77,f81])).

fof(f77,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

fof(f332,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | spl4_4 ),
    inference(forward_demodulation,[],[f331,f255])).

fof(f255,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(backward_demodulation,[],[f214,f252])).

fof(f331,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | spl4_4 ),
    inference(subsumption_resolution,[],[f330,f57])).

fof(f330,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f329,f63])).

fof(f63,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f49])).

fof(f329,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f328,f59])).

fof(f328,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f327,f206])).

fof(f206,plain,
    ( ~ v2_funct_1(sK3)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f204])).

fof(f327,plain,
    ( v2_funct_1(sK3)
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f132,f58])).

fof(f132,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,sK1,X2)
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | k1_xboole_0 = X2
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f131,f54])).

fof(f131,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f130,f55])).

fof(f130,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f128,f56])).

fof(f128,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,(
    ! [X2,X3] :
      ( sK1 != sK1
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2)))
      | ~ v1_funct_2(X3,sK1,X2)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(sK2,sK0,sK1)
      | ~ v1_funct_1(sK2) ) ),
    inference(superposition,[],[f75,f60])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f207,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f171,f204,f200])).

fof(f171,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f170,f57])).

fof(f170,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f169,f58])).

fof(f169,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f168,f59])).

fof(f168,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f159,f63])).

fof(f159,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f156])).

fof(f156,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f66,f153])).

fof(f195,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f193,f90])).

fof(f193,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl4_1 ),
    inference(resolution,[],[f192,f56])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f186,f88])).

fof(f186,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f184])).

fof(f191,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f182,f188,f184])).

fof(f182,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f110,f143])).

fof(f110,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f108,f54])).

fof(f108,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f69])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:48:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (12149)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (12143)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.19/0.52  % (12146)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.19/0.53  % (12155)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.19/0.53  % (12145)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.32/0.53  % (12134)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.32/0.54  % (12141)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.54  % (12136)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.32/0.54  % (12142)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.32/0.54  % (12162)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.32/0.54  % (12154)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.32/0.54  % (12137)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.32/0.54  % (12150)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.32/0.54  % (12151)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.32/0.54  % (12138)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.32/0.55  % (12161)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.32/0.55  % (12150)Refutation not found, incomplete strategy% (12150)------------------------------
% 1.32/0.55  % (12150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (12150)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (12150)Memory used [KB]: 10746
% 1.32/0.55  % (12150)Time elapsed: 0.127 s
% 1.32/0.55  % (12150)------------------------------
% 1.32/0.55  % (12150)------------------------------
% 1.32/0.55  % (12144)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.32/0.55  % (12159)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.32/0.55  % (12140)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.55  % (12135)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.32/0.55  % (12157)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.32/0.56  % (12158)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.32/0.56  % (12152)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.32/0.56  % (12163)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.32/0.56  % (12160)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.32/0.56  % (12144)Refutation not found, incomplete strategy% (12144)------------------------------
% 1.32/0.56  % (12144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (12144)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (12144)Memory used [KB]: 11001
% 1.32/0.56  % (12144)Time elapsed: 0.139 s
% 1.32/0.56  % (12144)------------------------------
% 1.32/0.56  % (12144)------------------------------
% 1.32/0.56  % (12153)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.32/0.57  % (12148)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.32/0.57  % (12162)Refutation not found, incomplete strategy% (12162)------------------------------
% 1.32/0.57  % (12162)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (12162)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.57  
% 1.32/0.57  % (12162)Memory used [KB]: 11001
% 1.32/0.57  % (12162)Time elapsed: 0.134 s
% 1.32/0.57  % (12162)------------------------------
% 1.32/0.57  % (12162)------------------------------
% 1.32/0.57  % (12156)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.32/0.57  % (12147)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.58  % (12139)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.32/0.59  % (12158)Refutation found. Thanks to Tanya!
% 1.32/0.59  % SZS status Theorem for theBenchmark
% 1.32/0.59  % SZS output start Proof for theBenchmark
% 1.32/0.59  fof(f523,plain,(
% 1.32/0.59    $false),
% 1.32/0.59    inference(avatar_sat_refutation,[],[f191,f195,f207,f334,f364,f368,f382,f443,f448,f487,f522])).
% 1.32/0.59  fof(f522,plain,(
% 1.32/0.59    ~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_10),
% 1.32/0.59    inference(avatar_contradiction_clause,[],[f521])).
% 1.32/0.59  fof(f521,plain,(
% 1.32/0.59    $false | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7 | ~spl4_10)),
% 1.32/0.59    inference(subsumption_resolution,[],[f520,f442])).
% 1.32/0.59  fof(f442,plain,(
% 1.32/0.59    sK0 = k1_relat_1(sK2) | ~spl4_10),
% 1.32/0.59    inference(avatar_component_clause,[],[f440])).
% 1.32/0.59  fof(f440,plain,(
% 1.32/0.59    spl4_10 <=> sK0 = k1_relat_1(sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.32/0.59  fof(f520,plain,(
% 1.32/0.59    sK0 != k1_relat_1(sK2) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(forward_demodulation,[],[f519,f176])).
% 1.32/0.59  fof(f176,plain,(
% 1.32/0.59    sK0 = k2_relat_1(sK3)),
% 1.32/0.59    inference(forward_demodulation,[],[f117,f153])).
% 1.32/0.59  fof(f153,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f152,f57])).
% 1.32/0.59  fof(f57,plain,(
% 1.32/0.59    v1_funct_1(sK3)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f49,plain,(
% 1.32/0.59    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.32/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f48,f47])).
% 1.32/0.59  fof(f47,plain,(
% 1.32/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.32/0.59    introduced(choice_axiom,[])).
% 1.32/0.59  fof(f48,plain,(
% 1.32/0.59    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.32/0.59    introduced(choice_axiom,[])).
% 1.32/0.59  fof(f23,plain,(
% 1.32/0.59    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.32/0.59    inference(flattening,[],[f22])).
% 1.32/0.59  fof(f22,plain,(
% 1.32/0.59    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.32/0.59    inference(ennf_transformation,[],[f21])).
% 1.32/0.59  fof(f21,negated_conjecture,(
% 1.32/0.59    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.32/0.59    inference(negated_conjecture,[],[f20])).
% 1.32/0.59  fof(f20,conjecture,(
% 1.32/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.32/0.59  fof(f152,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f151,f58])).
% 1.32/0.59  fof(f58,plain,(
% 1.32/0.59    v1_funct_2(sK3,sK1,sK0)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f151,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f150,f59])).
% 1.32/0.59  fof(f59,plain,(
% 1.32/0.59    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f150,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f149,f54])).
% 1.32/0.59  fof(f54,plain,(
% 1.32/0.59    v1_funct_1(sK2)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f149,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f148,f55])).
% 1.32/0.59  fof(f55,plain,(
% 1.32/0.59    v1_funct_2(sK2,sK0,sK1)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f148,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f146,f56])).
% 1.32/0.59  fof(f56,plain,(
% 1.32/0.59    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f146,plain,(
% 1.32/0.59    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.59    inference(resolution,[],[f61,f80])).
% 1.32/0.59  fof(f80,plain,(
% 1.32/0.59    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f37])).
% 1.32/0.59  fof(f37,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.32/0.59    inference(flattening,[],[f36])).
% 1.32/0.59  fof(f36,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.32/0.59    inference(ennf_transformation,[],[f17])).
% 1.32/0.59  fof(f17,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.32/0.59  fof(f61,plain,(
% 1.32/0.59    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f117,plain,(
% 1.32/0.59    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.32/0.59    inference(resolution,[],[f59,f85])).
% 1.32/0.59  fof(f85,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f42])).
% 1.32/0.59  fof(f42,plain,(
% 1.32/0.59    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.59    inference(ennf_transformation,[],[f11])).
% 1.32/0.59  fof(f11,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.32/0.59  fof(f519,plain,(
% 1.32/0.59    k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(trivial_inequality_removal,[],[f518])).
% 1.32/0.59  fof(f518,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(sK1) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(forward_demodulation,[],[f517,f143])).
% 1.32/0.59  fof(f143,plain,(
% 1.32/0.59    sK1 = k2_relat_1(sK2)),
% 1.32/0.59    inference(forward_demodulation,[],[f112,f60])).
% 1.32/0.59  fof(f60,plain,(
% 1.32/0.59    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f112,plain,(
% 1.32/0.59    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.32/0.59    inference(resolution,[],[f56,f85])).
% 1.32/0.59  fof(f517,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | (~spl4_1 | ~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f516,f185])).
% 1.32/0.59  fof(f185,plain,(
% 1.32/0.59    v1_relat_1(sK2) | ~spl4_1),
% 1.32/0.59    inference(avatar_component_clause,[],[f184])).
% 1.32/0.59  fof(f184,plain,(
% 1.32/0.59    spl4_1 <=> v1_relat_1(sK2)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.32/0.59  fof(f516,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f515,f54])).
% 1.32/0.59  fof(f515,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_5 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f514,f358])).
% 1.32/0.59  fof(f358,plain,(
% 1.32/0.59    v1_relat_1(sK3) | ~spl4_5),
% 1.32/0.59    inference(avatar_component_clause,[],[f357])).
% 1.32/0.59  fof(f357,plain,(
% 1.32/0.59    spl4_5 <=> v1_relat_1(sK3)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.32/0.59  fof(f514,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f513,f57])).
% 1.32/0.59  fof(f513,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f512,f62])).
% 1.32/0.59  fof(f62,plain,(
% 1.32/0.59    v2_funct_1(sK2)),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f512,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_7)),
% 1.32/0.59    inference(subsumption_resolution,[],[f510,f65])).
% 1.32/0.59  fof(f65,plain,(
% 1.32/0.59    k2_funct_1(sK2) != sK3),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f510,plain,(
% 1.32/0.59    k6_partfun1(sK1) != k6_partfun1(k2_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_3 | ~spl4_7)),
% 1.32/0.59    inference(superposition,[],[f97,f491])).
% 1.32/0.59  fof(f491,plain,(
% 1.32/0.59    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) | (~spl4_3 | ~spl4_7)),
% 1.32/0.59    inference(backward_demodulation,[],[f202,f377])).
% 1.32/0.59  fof(f377,plain,(
% 1.32/0.59    sK2 = k2_funct_1(sK3) | ~spl4_7),
% 1.32/0.59    inference(avatar_component_clause,[],[f375])).
% 1.32/0.59  fof(f375,plain,(
% 1.32/0.59    spl4_7 <=> sK2 = k2_funct_1(sK3)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.32/0.59  fof(f202,plain,(
% 1.32/0.59    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_3),
% 1.32/0.59    inference(avatar_component_clause,[],[f200])).
% 1.32/0.59  fof(f200,plain,(
% 1.32/0.59    spl4_3 <=> k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.32/0.59  fof(f97,plain,(
% 1.32/0.59    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(definition_unfolding,[],[f68,f81])).
% 1.32/0.59  fof(f81,plain,(
% 1.32/0.59    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f16])).
% 1.32/0.59  fof(f16,axiom,(
% 1.32/0.59    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.32/0.59  fof(f68,plain,(
% 1.32/0.59    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f27])).
% 1.32/0.59  fof(f27,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f26])).
% 1.32/0.59  fof(f26,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.59    inference(ennf_transformation,[],[f10])).
% 1.32/0.59  fof(f10,axiom,(
% 1.32/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.32/0.59  fof(f487,plain,(
% 1.32/0.59    ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_8),
% 1.32/0.59    inference(avatar_contradiction_clause,[],[f486])).
% 1.32/0.59  fof(f486,plain,(
% 1.32/0.59    $false | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_8)),
% 1.32/0.59    inference(subsumption_resolution,[],[f485,f358])).
% 1.32/0.59  fof(f485,plain,(
% 1.32/0.59    ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_8)),
% 1.32/0.59    inference(subsumption_resolution,[],[f483,f57])).
% 1.32/0.59  fof(f483,plain,(
% 1.32/0.59    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_8)),
% 1.32/0.59    inference(resolution,[],[f479,f71])).
% 1.32/0.59  fof(f71,plain,(
% 1.32/0.59    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f31])).
% 1.32/0.59  fof(f31,plain,(
% 1.32/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f30])).
% 1.32/0.59  fof(f30,plain,(
% 1.32/0.59    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.59    inference(ennf_transformation,[],[f7])).
% 1.32/0.59  fof(f7,axiom,(
% 1.32/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.32/0.59  fof(f479,plain,(
% 1.32/0.59    ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_8)),
% 1.32/0.59    inference(subsumption_resolution,[],[f478,f381])).
% 1.32/0.59  fof(f381,plain,(
% 1.32/0.59    sK1 != k1_relat_1(sK3) | spl4_8),
% 1.32/0.59    inference(avatar_component_clause,[],[f379])).
% 1.32/0.59  fof(f379,plain,(
% 1.32/0.59    spl4_8 <=> sK1 = k1_relat_1(sK3)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.32/0.59  fof(f478,plain,(
% 1.32/0.59    sK1 = k1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 1.32/0.59    inference(forward_demodulation,[],[f477,f370])).
% 1.32/0.59  fof(f370,plain,(
% 1.32/0.59    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | (~spl4_4 | ~spl4_5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f351,f358])).
% 1.32/0.59  fof(f351,plain,(
% 1.32/0.59    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.32/0.59    inference(subsumption_resolution,[],[f348,f57])).
% 1.32/0.59  fof(f348,plain,(
% 1.32/0.59    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.32/0.59    inference(resolution,[],[f205,f70])).
% 1.32/0.59  fof(f70,plain,(
% 1.32/0.59    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f29])).
% 1.32/0.59  fof(f29,plain,(
% 1.32/0.59    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f28])).
% 1.32/0.59  fof(f28,plain,(
% 1.32/0.59    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.32/0.59    inference(ennf_transformation,[],[f9])).
% 1.32/0.59  fof(f9,axiom,(
% 1.32/0.59    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.32/0.59  fof(f205,plain,(
% 1.32/0.59    v2_funct_1(sK3) | ~spl4_4),
% 1.32/0.59    inference(avatar_component_clause,[],[f204])).
% 1.32/0.59  fof(f204,plain,(
% 1.32/0.59    spl4_4 <=> v2_funct_1(sK3)),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.32/0.59  fof(f477,plain,(
% 1.32/0.59    sK1 = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 1.32/0.59    inference(forward_demodulation,[],[f476,f99])).
% 1.32/0.59  fof(f99,plain,(
% 1.32/0.59    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.32/0.59    inference(definition_unfolding,[],[f87,f81])).
% 1.32/0.59  fof(f87,plain,(
% 1.32/0.59    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.32/0.59    inference(cnf_transformation,[],[f6])).
% 1.32/0.59  fof(f6,axiom,(
% 1.32/0.59    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.32/0.59  fof(f476,plain,(
% 1.32/0.59    k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_3 | ~spl4_5 | ~spl4_6)),
% 1.32/0.59    inference(forward_demodulation,[],[f475,f202])).
% 1.32/0.59  fof(f475,plain,(
% 1.32/0.59    k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_5 | ~spl4_6)),
% 1.32/0.59    inference(subsumption_resolution,[],[f470,f106])).
% 1.32/0.59  fof(f106,plain,(
% 1.32/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.59    inference(equality_resolution,[],[f92])).
% 1.32/0.59  fof(f92,plain,(
% 1.32/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.32/0.59    inference(cnf_transformation,[],[f52])).
% 1.32/0.59  fof(f52,plain,(
% 1.32/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.59    inference(flattening,[],[f51])).
% 1.32/0.59  fof(f51,plain,(
% 1.32/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.32/0.59    inference(nnf_transformation,[],[f1])).
% 1.32/0.59  fof(f1,axiom,(
% 1.32/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.59  fof(f470,plain,(
% 1.32/0.59    ~r1_tarski(sK0,sK0) | k2_relat_1(k2_funct_1(sK3)) = k2_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | (~spl4_5 | ~spl4_6)),
% 1.32/0.59    inference(superposition,[],[f449,f363])).
% 1.32/0.59  fof(f363,plain,(
% 1.32/0.59    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~spl4_6),
% 1.32/0.59    inference(avatar_component_clause,[],[f361])).
% 1.32/0.59  fof(f361,plain,(
% 1.32/0.59    spl4_6 <=> sK0 = k1_relat_1(k2_funct_1(sK3))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.32/0.59  fof(f449,plain,(
% 1.32/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),sK0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) | ~v1_relat_1(X0)) ) | ~spl4_5),
% 1.32/0.59    inference(subsumption_resolution,[],[f177,f358])).
% 1.32/0.59  fof(f177,plain,(
% 1.32/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),sK0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) | ~v1_relat_1(sK3) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(superposition,[],[f91,f176])).
% 1.32/0.59  fof(f91,plain,(
% 1.32/0.59    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f45])).
% 1.32/0.59  fof(f45,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(flattening,[],[f44])).
% 1.32/0.59  fof(f44,plain,(
% 1.32/0.59    ! [X0] : (! [X1] : ((k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0) | ~r1_tarski(k1_relat_1(X0),k2_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.32/0.59    inference(ennf_transformation,[],[f5])).
% 1.32/0.59  fof(f5,axiom,(
% 1.32/0.59    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) => k2_relat_1(k5_relat_1(X1,X0)) = k2_relat_1(X0))))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_relat_1)).
% 1.32/0.59  fof(f448,plain,(
% 1.32/0.59    ~spl4_1 | spl4_9),
% 1.32/0.59    inference(avatar_contradiction_clause,[],[f447])).
% 1.32/0.59  fof(f447,plain,(
% 1.32/0.59    $false | (~spl4_1 | spl4_9)),
% 1.32/0.59    inference(subsumption_resolution,[],[f446,f185])).
% 1.32/0.59  fof(f446,plain,(
% 1.32/0.59    ~v1_relat_1(sK2) | spl4_9),
% 1.32/0.59    inference(subsumption_resolution,[],[f444,f54])).
% 1.32/0.59  fof(f444,plain,(
% 1.32/0.59    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl4_9),
% 1.32/0.59    inference(resolution,[],[f438,f71])).
% 1.32/0.59  fof(f438,plain,(
% 1.32/0.59    ~v1_relat_1(k2_funct_1(sK2)) | spl4_9),
% 1.32/0.59    inference(avatar_component_clause,[],[f436])).
% 1.32/0.59  fof(f436,plain,(
% 1.32/0.59    spl4_9 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.32/0.59  fof(f443,plain,(
% 1.32/0.59    ~spl4_9 | spl4_10 | ~spl4_1 | ~spl4_2),
% 1.32/0.59    inference(avatar_split_clause,[],[f433,f188,f184,f440,f436])).
% 1.32/0.59  fof(f188,plain,(
% 1.32/0.59    spl4_2 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 1.32/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.32/0.59  fof(f433,plain,(
% 1.32/0.59    sK0 = k1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.32/0.59    inference(forward_demodulation,[],[f432,f197])).
% 1.32/0.59  fof(f197,plain,(
% 1.32/0.59    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl4_1),
% 1.32/0.59    inference(subsumption_resolution,[],[f111,f185])).
% 1.32/0.59  fof(f111,plain,(
% 1.32/0.59    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f109,f54])).
% 1.32/0.59  fof(f109,plain,(
% 1.32/0.59    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.32/0.59    inference(resolution,[],[f62,f70])).
% 1.32/0.59  fof(f432,plain,(
% 1.32/0.59    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.32/0.59    inference(forward_demodulation,[],[f431,f99])).
% 1.32/0.59  fof(f431,plain,(
% 1.32/0.59    k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.32/0.59    inference(forward_demodulation,[],[f430,f137])).
% 1.32/0.59  fof(f137,plain,(
% 1.32/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.32/0.59    inference(subsumption_resolution,[],[f136,f54])).
% 1.32/0.59  fof(f136,plain,(
% 1.32/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f135,f55])).
% 1.32/0.59  fof(f135,plain,(
% 1.32/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f134,f56])).
% 1.32/0.59  fof(f134,plain,(
% 1.32/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f133,f62])).
% 1.32/0.59  fof(f133,plain,(
% 1.32/0.59    ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f127,f64])).
% 1.32/0.59  fof(f64,plain,(
% 1.32/0.59    k1_xboole_0 != sK1),
% 1.32/0.59    inference(cnf_transformation,[],[f49])).
% 1.32/0.59  fof(f127,plain,(
% 1.32/0.59    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(trivial_inequality_removal,[],[f124])).
% 1.32/0.59  fof(f124,plain,(
% 1.32/0.59    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.32/0.59    inference(superposition,[],[f66,f60])).
% 1.32/0.59  fof(f66,plain,(
% 1.32/0.59    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.32/0.59    inference(cnf_transformation,[],[f25])).
% 1.32/0.59  fof(f25,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.32/0.59    inference(flattening,[],[f24])).
% 1.32/0.59  fof(f24,plain,(
% 1.32/0.59    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.32/0.59    inference(ennf_transformation,[],[f19])).
% 1.32/0.59  fof(f19,axiom,(
% 1.32/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.32/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.32/0.59  fof(f430,plain,(
% 1.32/0.59    k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.32/0.59    inference(subsumption_resolution,[],[f427,f106])).
% 1.32/0.59  fof(f427,plain,(
% 1.32/0.59    ~r1_tarski(sK1,sK1) | k2_relat_1(k2_funct_1(sK2)) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl4_1 | ~spl4_2)),
% 1.32/0.59    inference(superposition,[],[f383,f190])).
% 1.32/0.59  fof(f190,plain,(
% 1.32/0.59    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl4_2),
% 1.32/0.59    inference(avatar_component_clause,[],[f188])).
% 1.32/0.59  fof(f383,plain,(
% 1.32/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),sK1) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(X0)) ) | ~spl4_1),
% 1.32/0.59    inference(subsumption_resolution,[],[f144,f185])).
% 1.32/0.59  fof(f144,plain,(
% 1.32/0.59    ( ! [X0] : (~r1_tarski(k1_relat_1(X0),sK1) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK2,X0)) | ~v1_relat_1(sK2) | ~v1_relat_1(X0)) )),
% 1.32/0.59    inference(superposition,[],[f91,f143])).
% 1.32/0.59  fof(f382,plain,(
% 1.32/0.59    spl4_7 | ~spl4_8 | ~spl4_1 | ~spl4_4 | ~spl4_5),
% 1.32/0.59    inference(avatar_split_clause,[],[f372,f357,f204,f184,f379,f375])).
% 1.32/0.59  fof(f372,plain,(
% 1.32/0.59    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | (~spl4_1 | ~spl4_4 | ~spl4_5)),
% 1.32/0.59    inference(subsumption_resolution,[],[f371,f358])).
% 1.32/0.59  fof(f371,plain,(
% 1.32/0.59    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_1 | ~spl4_4)),
% 1.32/0.59    inference(subsumption_resolution,[],[f345,f205])).
% 1.32/0.59  fof(f345,plain,(
% 1.32/0.59    sK1 != k1_relat_1(sK3) | sK2 = k2_funct_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_1),
% 1.32/0.59    inference(forward_demodulation,[],[f344,f143])).
% 1.32/0.59  fof(f344,plain,(
% 1.32/0.59    sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_1),
% 1.32/0.59    inference(trivial_inequality_removal,[],[f343])).
% 1.32/0.59  fof(f343,plain,(
% 1.32/0.59    k6_partfun1(sK0) != k6_partfun1(sK0) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_1),
% 1.32/0.59    inference(forward_demodulation,[],[f342,f176])).
% 1.32/0.59  fof(f342,plain,(
% 1.32/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_1),
% 1.32/0.59    inference(subsumption_resolution,[],[f341,f57])).
% 1.32/0.59  fof(f341,plain,(
% 1.32/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_1),
% 1.32/0.59    inference(subsumption_resolution,[],[f340,f185])).
% 1.32/0.59  fof(f340,plain,(
% 1.32/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.32/0.59    inference(subsumption_resolution,[],[f256,f54])).
% 1.32/0.59  fof(f256,plain,(
% 1.32/0.59    k6_partfun1(sK0) != k6_partfun1(k2_relat_1(sK3)) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)),
% 1.32/0.59    inference(superposition,[],[f97,f252])).
% 1.32/0.59  fof(f252,plain,(
% 1.32/0.59    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.32/0.59    inference(global_subsumption,[],[f249,f251])).
% 1.32/0.60  fof(f251,plain,(
% 1.32/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.32/0.60    inference(subsumption_resolution,[],[f250,f101])).
% 1.32/0.60  fof(f101,plain,(
% 1.32/0.60    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.32/0.60    inference(definition_unfolding,[],[f89,f81])).
% 1.32/0.60  fof(f89,plain,(
% 1.32/0.60    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.32/0.60    inference(cnf_transformation,[],[f13])).
% 1.32/0.60  fof(f13,axiom,(
% 1.32/0.60    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.32/0.60  fof(f250,plain,(
% 1.32/0.60    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.32/0.60    inference(resolution,[],[f238,f78])).
% 1.32/0.60  fof(f78,plain,(
% 1.32/0.60    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.32/0.60    inference(cnf_transformation,[],[f50])).
% 1.32/0.60  fof(f50,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.60    inference(nnf_transformation,[],[f35])).
% 1.32/0.60  fof(f35,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.32/0.60    inference(flattening,[],[f34])).
% 1.32/0.60  fof(f34,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.32/0.60    inference(ennf_transformation,[],[f12])).
% 1.32/0.60  fof(f12,axiom,(
% 1.32/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.32/0.60  fof(f238,plain,(
% 1.32/0.60    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 1.32/0.60    inference(backward_demodulation,[],[f61,f214])).
% 1.32/0.60  fof(f214,plain,(
% 1.32/0.60    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.32/0.60    inference(subsumption_resolution,[],[f211,f57])).
% 1.32/0.60  fof(f211,plain,(
% 1.32/0.60    ~v1_funct_1(sK3) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.32/0.60    inference(resolution,[],[f115,f59])).
% 1.32/0.60  fof(f115,plain,(
% 1.32/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0)) )),
% 1.32/0.60    inference(subsumption_resolution,[],[f113,f54])).
% 1.32/0.60  fof(f113,plain,(
% 1.32/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK2,X0) = k5_relat_1(sK2,X0) | ~v1_funct_1(sK2)) )),
% 1.32/0.60    inference(resolution,[],[f56,f84])).
% 1.32/0.60  fof(f84,plain,(
% 1.32/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X4)) )),
% 1.32/0.60    inference(cnf_transformation,[],[f41])).
% 1.32/0.60  fof(f41,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.32/0.60    inference(flattening,[],[f40])).
% 1.32/0.60  fof(f40,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.32/0.60    inference(ennf_transformation,[],[f15])).
% 1.32/0.60  fof(f15,axiom,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.32/0.60  fof(f249,plain,(
% 1.32/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.32/0.60    inference(subsumption_resolution,[],[f248,f54])).
% 1.32/0.60  fof(f248,plain,(
% 1.32/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 1.32/0.60    inference(subsumption_resolution,[],[f247,f56])).
% 1.32/0.60  fof(f247,plain,(
% 1.32/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.32/0.60    inference(subsumption_resolution,[],[f246,f57])).
% 1.32/0.60  fof(f246,plain,(
% 1.32/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.32/0.60    inference(subsumption_resolution,[],[f241,f59])).
% 1.32/0.60  fof(f241,plain,(
% 1.32/0.60    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.32/0.60    inference(superposition,[],[f83,f214])).
% 1.32/0.60  fof(f83,plain,(
% 1.32/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.32/0.60    inference(cnf_transformation,[],[f39])).
% 1.32/0.60  fof(f39,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.32/0.60    inference(flattening,[],[f38])).
% 1.32/0.60  fof(f38,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.32/0.60    inference(ennf_transformation,[],[f14])).
% 1.32/0.60  fof(f14,axiom,(
% 1.32/0.60    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.32/0.60  fof(f368,plain,(
% 1.32/0.60    spl4_5),
% 1.32/0.60    inference(avatar_contradiction_clause,[],[f367])).
% 1.32/0.60  fof(f367,plain,(
% 1.32/0.60    $false | spl4_5),
% 1.32/0.60    inference(subsumption_resolution,[],[f366,f90])).
% 1.32/0.60  fof(f90,plain,(
% 1.32/0.60    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.32/0.60    inference(cnf_transformation,[],[f4])).
% 1.32/0.60  fof(f4,axiom,(
% 1.32/0.60    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.32/0.60  fof(f366,plain,(
% 1.32/0.60    ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | spl4_5),
% 1.32/0.60    inference(resolution,[],[f365,f59])).
% 1.32/0.60  fof(f365,plain,(
% 1.32/0.60    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_5),
% 1.32/0.60    inference(resolution,[],[f359,f88])).
% 1.32/0.60  fof(f88,plain,(
% 1.32/0.60    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.32/0.60    inference(cnf_transformation,[],[f43])).
% 1.32/0.60  fof(f43,plain,(
% 1.32/0.60    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.32/0.60    inference(ennf_transformation,[],[f2])).
% 1.32/0.60  fof(f2,axiom,(
% 1.32/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.32/0.60  fof(f359,plain,(
% 1.32/0.60    ~v1_relat_1(sK3) | spl4_5),
% 1.32/0.60    inference(avatar_component_clause,[],[f357])).
% 1.32/0.60  fof(f364,plain,(
% 1.32/0.60    ~spl4_5 | spl4_6 | ~spl4_4),
% 1.32/0.60    inference(avatar_split_clause,[],[f350,f204,f361,f357])).
% 1.32/0.60  fof(f350,plain,(
% 1.32/0.60    sK0 = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.32/0.60    inference(forward_demodulation,[],[f349,f176])).
% 1.32/0.60  fof(f349,plain,(
% 1.32/0.60    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f347,f57])).
% 1.32/0.60  fof(f347,plain,(
% 1.32/0.60    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_4),
% 1.32/0.60    inference(resolution,[],[f205,f69])).
% 1.32/0.60  fof(f69,plain,(
% 1.32/0.60    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.32/0.60    inference(cnf_transformation,[],[f29])).
% 1.32/0.60  fof(f334,plain,(
% 1.32/0.60    spl4_4),
% 1.32/0.60    inference(avatar_contradiction_clause,[],[f333])).
% 1.32/0.60  fof(f333,plain,(
% 1.32/0.60    $false | spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f332,f98])).
% 1.32/0.60  fof(f98,plain,(
% 1.32/0.60    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.32/0.60    inference(definition_unfolding,[],[f77,f81])).
% 1.32/0.60  fof(f77,plain,(
% 1.32/0.60    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.32/0.60    inference(cnf_transformation,[],[f8])).
% 1.32/0.60  fof(f8,axiom,(
% 1.32/0.60    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).
% 1.32/0.60  fof(f332,plain,(
% 1.32/0.60    ~v2_funct_1(k6_partfun1(sK0)) | spl4_4),
% 1.32/0.60    inference(forward_demodulation,[],[f331,f255])).
% 1.32/0.60  fof(f255,plain,(
% 1.32/0.60    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.32/0.60    inference(backward_demodulation,[],[f214,f252])).
% 1.32/0.60  fof(f331,plain,(
% 1.32/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f330,f57])).
% 1.32/0.60  fof(f330,plain,(
% 1.32/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~v1_funct_1(sK3) | spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f329,f63])).
% 1.32/0.60  fof(f63,plain,(
% 1.32/0.60    k1_xboole_0 != sK0),
% 1.32/0.60    inference(cnf_transformation,[],[f49])).
% 1.32/0.60  fof(f329,plain,(
% 1.32/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f328,f59])).
% 1.32/0.60  fof(f328,plain,(
% 1.32/0.60    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3) | spl4_4),
% 1.32/0.60    inference(subsumption_resolution,[],[f327,f206])).
% 1.32/0.60  fof(f206,plain,(
% 1.32/0.60    ~v2_funct_1(sK3) | spl4_4),
% 1.32/0.60    inference(avatar_component_clause,[],[f204])).
% 1.32/0.60  fof(f327,plain,(
% 1.32/0.60    v2_funct_1(sK3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(resolution,[],[f132,f58])).
% 1.32/0.60  fof(f132,plain,(
% 1.32/0.60    ( ! [X2,X3] : (~v1_funct_2(X3,sK1,X2) | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | k1_xboole_0 = X2 | ~v1_funct_1(X3)) )),
% 1.32/0.60    inference(subsumption_resolution,[],[f131,f54])).
% 1.32/0.60  fof(f131,plain,(
% 1.32/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_1(sK2)) )),
% 1.32/0.60    inference(subsumption_resolution,[],[f130,f55])).
% 1.32/0.60  fof(f130,plain,(
% 1.32/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.32/0.60    inference(subsumption_resolution,[],[f128,f56])).
% 1.32/0.60  fof(f128,plain,(
% 1.32/0.60    ( ! [X2,X3] : (k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.32/0.60    inference(trivial_inequality_removal,[],[f123])).
% 1.32/0.60  fof(f123,plain,(
% 1.32/0.60    ( ! [X2,X3] : (sK1 != sK1 | k1_xboole_0 = X2 | v2_funct_1(X3) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X2,sK2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,X2))) | ~v1_funct_2(X3,sK1,X2) | ~v1_funct_1(X3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) )),
% 1.32/0.60    inference(superposition,[],[f75,f60])).
% 1.32/0.60  fof(f75,plain,(
% 1.32/0.60    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.32/0.60    inference(cnf_transformation,[],[f33])).
% 1.32/0.60  fof(f33,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.32/0.60    inference(flattening,[],[f32])).
% 1.32/0.60  fof(f32,plain,(
% 1.32/0.60    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.32/0.60    inference(ennf_transformation,[],[f18])).
% 1.32/0.60  fof(f18,axiom,(
% 1.32/0.60    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.32/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.32/0.60  fof(f207,plain,(
% 1.32/0.60    spl4_3 | ~spl4_4),
% 1.32/0.60    inference(avatar_split_clause,[],[f171,f204,f200])).
% 1.32/0.60  fof(f171,plain,(
% 1.32/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.32/0.60    inference(subsumption_resolution,[],[f170,f57])).
% 1.32/0.60  fof(f170,plain,(
% 1.32/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(subsumption_resolution,[],[f169,f58])).
% 1.32/0.60  fof(f169,plain,(
% 1.32/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(subsumption_resolution,[],[f168,f59])).
% 1.32/0.60  fof(f168,plain,(
% 1.32/0.60    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(subsumption_resolution,[],[f159,f63])).
% 1.32/0.60  fof(f159,plain,(
% 1.32/0.60    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(trivial_inequality_removal,[],[f156])).
% 1.32/0.60  fof(f156,plain,(
% 1.32/0.60    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.32/0.60    inference(superposition,[],[f66,f153])).
% 1.32/0.60  fof(f195,plain,(
% 1.32/0.60    spl4_1),
% 1.32/0.60    inference(avatar_contradiction_clause,[],[f194])).
% 1.32/0.60  fof(f194,plain,(
% 1.32/0.60    $false | spl4_1),
% 1.32/0.60    inference(subsumption_resolution,[],[f193,f90])).
% 1.32/0.60  fof(f193,plain,(
% 1.32/0.60    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl4_1),
% 1.32/0.60    inference(resolution,[],[f192,f56])).
% 1.32/0.60  fof(f192,plain,(
% 1.32/0.60    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl4_1),
% 1.32/0.60    inference(resolution,[],[f186,f88])).
% 1.32/0.60  fof(f186,plain,(
% 1.32/0.60    ~v1_relat_1(sK2) | spl4_1),
% 1.32/0.60    inference(avatar_component_clause,[],[f184])).
% 1.32/0.60  fof(f191,plain,(
% 1.32/0.60    ~spl4_1 | spl4_2),
% 1.32/0.60    inference(avatar_split_clause,[],[f182,f188,f184])).
% 1.32/0.60  fof(f182,plain,(
% 1.32/0.60    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.32/0.60    inference(forward_demodulation,[],[f110,f143])).
% 1.32/0.60  fof(f110,plain,(
% 1.32/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.32/0.60    inference(subsumption_resolution,[],[f108,f54])).
% 1.32/0.60  fof(f108,plain,(
% 1.32/0.60    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.32/0.60    inference(resolution,[],[f62,f69])).
% 1.32/0.60  % SZS output end Proof for theBenchmark
% 1.32/0.60  % (12158)------------------------------
% 1.32/0.60  % (12158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.60  % (12158)Termination reason: Refutation
% 1.32/0.60  
% 1.32/0.60  % (12158)Memory used [KB]: 11001
% 1.32/0.60  % (12158)Time elapsed: 0.166 s
% 1.32/0.60  % (12158)------------------------------
% 1.32/0.60  % (12158)------------------------------
% 1.32/0.60  % (12133)Success in time 0.235 s
%------------------------------------------------------------------------------
