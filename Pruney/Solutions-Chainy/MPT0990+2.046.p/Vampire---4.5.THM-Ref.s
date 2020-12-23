%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:36 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  164 ( 982 expanded)
%              Number of leaves         :   22 ( 310 expanded)
%              Depth                    :   29
%              Number of atoms          :  702 (9920 expanded)
%              Number of equality atoms :  234 (3461 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f347,f620,f640,f1244])).

fof(f1244,plain,
    ( ~ spl5_9
    | ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f1243])).

fof(f1243,plain,
    ( $false
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1242,f96])).

fof(f96,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( k2_funct_1(sK3) != sK4
    & k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & v2_funct_1(sK3)
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & sK2 = k2_relset_1(sK1,sK2,sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f41,f40])).

fof(f40,plain,
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
          ( k2_funct_1(sK3) != X3
          & k1_xboole_0 != sK2
          & k1_xboole_0 != sK1
          & v2_funct_1(sK3)
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & sK2 = k2_relset_1(sK1,sK2,sK3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( k2_funct_1(sK3) != X3
        & k1_xboole_0 != sK2
        & k1_xboole_0 != sK1
        & v2_funct_1(sK3)
        & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
        & sK2 = k2_relset_1(sK1,sK2,sK3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X3,sK2,sK1)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK3) != sK4
      & k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & v2_funct_1(sK3)
      & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
      & sK2 = k2_relset_1(sK1,sK2,sK3)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1242,plain,
    ( ~ v1_relat_1(sK4)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1241,f50])).

fof(f50,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f1241,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1240,f58])).

fof(f58,plain,(
    k2_funct_1(sK3) != sK4 ),
    inference(cnf_transformation,[],[f42])).

fof(f1240,plain,
    ( k2_funct_1(sK3) = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1239,f314])).

fof(f314,plain,(
    sK1 = k2_relat_1(sK4) ),
    inference(backward_demodulation,[],[f108,f313])).

fof(f313,plain,(
    sK1 = k2_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f312,f50])).

fof(f312,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f311,f51])).

fof(f51,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f311,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f310,f52])).

fof(f310,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f309,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f309,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f308,f48])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f308,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f307,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f42])).

fof(f307,plain,
    ( sK1 = k2_relset_1(sK2,sK1,sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_2(sK3,sK1,sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(resolution,[],[f78,f54])).

fof(f54,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

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

fof(f108,plain,(
    k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(resolution,[],[f68,f52])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f1239,plain,
    ( sK1 != k2_relat_1(sK4)
    | k2_funct_1(sK3) = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f1238])).

fof(f1238,plain,
    ( k6_partfun1(sK2) != k6_partfun1(sK2)
    | sK1 != k2_relat_1(sK4)
    | k2_funct_1(sK3) = sK4
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(superposition,[],[f198,f1212])).

fof(f1212,plain,
    ( k6_partfun1(sK2) = k5_relat_1(sK4,sK3)
    | ~ spl5_9
    | ~ spl5_24 ),
    inference(backward_demodulation,[],[f282,f1209])).

fof(f1209,plain,
    ( sK3 = k2_funct_1(sK4)
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1208,f110])).

fof(f110,plain,(
    sK2 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f107,f53])).

fof(f53,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f107,plain,(
    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f68,f49])).

fof(f1208,plain,
    ( sK3 = k2_funct_1(sK4)
    | sK2 != k2_relat_1(sK3)
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1207,f47])).

fof(f1207,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK4)
    | sK2 != k2_relat_1(sK3)
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f1206,f95])).

fof(f95,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f66,f49])).

fof(f1206,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK4)
    | sK2 != k2_relat_1(sK3)
    | ~ spl5_24 ),
    inference(trivial_inequality_removal,[],[f1204])).

fof(f1204,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(sK4)
    | sK2 != k2_relat_1(sK3)
    | ~ spl5_24 ),
    inference(superposition,[],[f639,f459])).

fof(f459,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) ),
    inference(global_subsumption,[],[f453,f458])).

fof(f458,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,sK4)
    | ~ m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(resolution,[],[f441,f189])).

fof(f189,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_partfun1(X2))
      | k6_partfun1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f79,f84])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f33])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f441,plain,(
    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) ),
    inference(backward_demodulation,[],[f54,f380])).

fof(f380,plain,(
    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f376,f47])).

fof(f376,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f205,f49])).

fof(f205,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f202,f50])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f81,f52])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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

fof(f453,plain,(
    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f452,f47])).

fof(f452,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f451,f49])).

fof(f451,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f450,f50])).

fof(f450,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f443,f52])).

fof(f443,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f83,f380])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f639,plain,
    ( ! [X0] :
        ( k6_partfun1(sK1) != k5_relat_1(X0,sK4)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(sK4) = X0
        | k2_relat_1(X0) != sK2 )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f638])).

fof(f638,plain,
    ( spl5_24
  <=> ! [X0] :
        ( k2_relat_1(X0) != sK2
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(sK4) = X0
        | k6_partfun1(sK1) != k5_relat_1(X0,sK4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f282,plain,
    ( k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f280])).

fof(f280,plain,
    ( spl5_9
  <=> k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f198,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_partfun1(sK2)
      | k2_relat_1(X0) != sK1
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f197,f138])).

fof(f138,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f104,f130])).

fof(f130,plain,(
    sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f129,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(subsumption_resolution,[],[f126,f48])).

fof(f126,plain,
    ( ~ v1_funct_2(sK3,sK1,sK2)
    | k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK3) ),
    inference(resolution,[],[f69,f98])).

fof(f98,plain,(
    sP0(sK1,sK3,sK2) ),
    inference(resolution,[],[f73,f49])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP0(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & sP0(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ v1_funct_2(X1,X0,X2)
      | k1_xboole_0 = X2
      | k1_relset_1(X0,X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f104,plain,(
    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f67,f49])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f197,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_partfun1(sK2)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f196,f95])).

fof(f196,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_partfun1(sK2)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f195,f47])).

fof(f195,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_partfun1(sK2)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f194,f55])).

fof(f55,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f194,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK3) != k6_partfun1(sK2)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3)
      | ~ v2_funct_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(superposition,[],[f87,f110])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f63,f59])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f640,plain,
    ( ~ spl5_3
    | spl5_24 ),
    inference(avatar_split_clause,[],[f636,f638,f158])).

fof(f158,plain,
    ( spl5_3
  <=> v2_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f636,plain,(
    ! [X0] :
      ( k2_relat_1(X0) != sK2
      | k6_partfun1(sK1) != k5_relat_1(X0,sK4)
      | k2_funct_1(sK4) = X0
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f635,f141])).

fof(f141,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f105,f132])).

fof(f132,plain,(
    sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f56,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f131,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(subsumption_resolution,[],[f127,f51])).

fof(f127,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | k1_xboole_0 = sK1
    | sK2 = k1_relset_1(sK2,sK1,sK4) ),
    inference(resolution,[],[f69,f99])).

fof(f99,plain,(
    sP0(sK2,sK4,sK1) ),
    inference(resolution,[],[f73,f52])).

fof(f105,plain,(
    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4) ),
    inference(resolution,[],[f67,f52])).

fof(f635,plain,(
    ! [X0] :
      ( k6_partfun1(sK1) != k5_relat_1(X0,sK4)
      | k2_funct_1(sK4) = X0
      | k2_relat_1(X0) != k1_relat_1(sK4)
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f634,f96])).

fof(f634,plain,(
    ! [X0] :
      ( k6_partfun1(sK1) != k5_relat_1(X0,sK4)
      | k2_funct_1(sK4) = X0
      | k2_relat_1(X0) != k1_relat_1(sK4)
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f354,f50])).

fof(f354,plain,(
    ! [X0] :
      ( k6_partfun1(sK1) != k5_relat_1(X0,sK4)
      | k2_funct_1(sK4) = X0
      | k2_relat_1(X0) != k1_relat_1(sK4)
      | ~ v2_funct_1(sK4)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f87,f314])).

fof(f620,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f619])).

fof(f619,plain,
    ( $false
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f618,f85])).

fof(f85,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f59])).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f618,plain,
    ( ~ v2_funct_1(k6_partfun1(sK1))
    | ~ spl5_4 ),
    inference(forward_demodulation,[],[f617,f459])).

fof(f617,plain,
    ( ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f616,f47])).

fof(f616,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f615,f95])).

fof(f615,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_4 ),
    inference(trivial_inequality_removal,[],[f613])).

fof(f613,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(k5_relat_1(sK3,sK4))
    | ~ spl5_4 ),
    inference(superposition,[],[f163,f110])).

fof(f163,plain,
    ( ! [X1] :
        ( k2_relat_1(X1) != sK2
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK4)) )
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl5_4
  <=> ! [X1] :
        ( k2_relat_1(X1) != sK2
        | ~ v1_relat_1(X1)
        | ~ v1_funct_1(X1)
        | ~ v2_funct_1(k5_relat_1(X1,sK4)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f347,plain,
    ( spl5_9
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f346,f158,f280])).

fof(f346,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) ),
    inference(global_subsumption,[],[f333])).

fof(f333,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) ),
    inference(subsumption_resolution,[],[f332,f50])).

fof(f332,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f331,f51])).

fof(f331,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f326,f52])).

fof(f326,plain,
    ( ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f317,f56])).

fof(f317,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(trivial_inequality_removal,[],[f316])).

fof(f316,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK4)
    | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4) ),
    inference(superposition,[],[f76,f313])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f164,plain,
    ( spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f156,f162,f158])).

fof(f156,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK2
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X1,sK4))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f155,f96])).

fof(f155,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK2
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X1,sK4))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(subsumption_resolution,[],[f154,f50])).

fof(f154,plain,(
    ! [X1] :
      ( k2_relat_1(X1) != sK2
      | v2_funct_1(sK4)
      | ~ v2_funct_1(k5_relat_1(X1,sK4))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(sK4)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f65,f141])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:32:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (4391)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (4407)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (4399)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.51  % (4394)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.51  % (4393)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (4395)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (4408)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (4400)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (4390)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (4389)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.53  % (4388)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (4385)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (4387)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (4414)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (4404)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (4405)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (4406)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.38/0.54  % (4397)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.54  % (4392)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.54  % (4412)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.54  % (4386)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.54  % (4395)Refutation not found, incomplete strategy% (4395)------------------------------
% 1.38/0.54  % (4395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.54  % (4395)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.54  
% 1.38/0.54  % (4395)Memory used [KB]: 11001
% 1.38/0.54  % (4395)Time elapsed: 0.131 s
% 1.38/0.54  % (4395)------------------------------
% 1.38/0.54  % (4395)------------------------------
% 1.38/0.54  % (4413)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.54  % (4411)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.38/0.54  % (4409)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.38/0.54  % (4398)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.54  % (4403)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.55  % (4396)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.55  % (4413)Refutation not found, incomplete strategy% (4413)------------------------------
% 1.38/0.55  % (4413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (4413)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (4413)Memory used [KB]: 11001
% 1.38/0.55  % (4413)Time elapsed: 0.148 s
% 1.38/0.55  % (4413)------------------------------
% 1.38/0.55  % (4413)------------------------------
% 1.38/0.55  % (4401)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.38/0.55  % (4410)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (4401)Refutation not found, incomplete strategy% (4401)------------------------------
% 1.38/0.55  % (4401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (4401)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (4401)Memory used [KB]: 10746
% 1.38/0.55  % (4401)Time elapsed: 0.150 s
% 1.38/0.55  % (4401)------------------------------
% 1.38/0.55  % (4401)------------------------------
% 1.54/0.56  % (4402)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.54/0.56  % (4391)Refutation found. Thanks to Tanya!
% 1.54/0.56  % SZS status Theorem for theBenchmark
% 1.54/0.56  % SZS output start Proof for theBenchmark
% 1.54/0.56  fof(f1245,plain,(
% 1.54/0.56    $false),
% 1.54/0.56    inference(avatar_sat_refutation,[],[f164,f347,f620,f640,f1244])).
% 1.54/0.56  fof(f1244,plain,(
% 1.54/0.56    ~spl5_9 | ~spl5_24),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f1243])).
% 1.54/0.56  fof(f1243,plain,(
% 1.54/0.56    $false | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(subsumption_resolution,[],[f1242,f96])).
% 1.54/0.56  fof(f96,plain,(
% 1.54/0.56    v1_relat_1(sK4)),
% 1.54/0.56    inference(resolution,[],[f66,f52])).
% 1.54/0.56  fof(f52,plain,(
% 1.54/0.56    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f42,plain,(
% 1.54/0.56    (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 1.54/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f18,f41,f40])).
% 1.54/0.56  fof(f40,plain,(
% 1.54/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f41,plain,(
% 1.54/0.56    ? [X3] : (k2_funct_1(sK3) != X3 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) => (k2_funct_1(sK3) != sK4 & k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & v2_funct_1(sK3) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & sK2 = k2_relset_1(sK1,sK2,sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 1.54/0.56    introduced(choice_axiom,[])).
% 1.54/0.56  fof(f18,plain,(
% 1.54/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.54/0.56    inference(flattening,[],[f17])).
% 1.54/0.56  fof(f17,plain,(
% 1.54/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f16])).
% 1.54/0.56  fof(f16,negated_conjecture,(
% 1.54/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.56    inference(negated_conjecture,[],[f15])).
% 1.54/0.56  fof(f15,conjecture,(
% 1.54/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.54/0.56  fof(f66,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f23])).
% 1.54/0.56  fof(f23,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(ennf_transformation,[],[f4])).
% 1.54/0.56  fof(f4,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.54/0.56  fof(f1242,plain,(
% 1.54/0.56    ~v1_relat_1(sK4) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(subsumption_resolution,[],[f1241,f50])).
% 1.54/0.56  fof(f50,plain,(
% 1.54/0.56    v1_funct_1(sK4)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f1241,plain,(
% 1.54/0.56    ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(subsumption_resolution,[],[f1240,f58])).
% 1.54/0.56  fof(f58,plain,(
% 1.54/0.56    k2_funct_1(sK3) != sK4),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f1240,plain,(
% 1.54/0.56    k2_funct_1(sK3) = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(subsumption_resolution,[],[f1239,f314])).
% 1.54/0.56  fof(f314,plain,(
% 1.54/0.56    sK1 = k2_relat_1(sK4)),
% 1.54/0.56    inference(backward_demodulation,[],[f108,f313])).
% 1.54/0.56  fof(f313,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f312,f50])).
% 1.54/0.56  fof(f312,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f311,f51])).
% 1.54/0.56  fof(f51,plain,(
% 1.54/0.56    v1_funct_2(sK4,sK2,sK1)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f311,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f310,f52])).
% 1.54/0.56  fof(f310,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f309,f47])).
% 1.54/0.56  fof(f47,plain,(
% 1.54/0.56    v1_funct_1(sK3)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f309,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f308,f48])).
% 1.54/0.56  fof(f48,plain,(
% 1.54/0.56    v1_funct_2(sK3,sK1,sK2)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f308,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f307,f49])).
% 1.54/0.56  fof(f49,plain,(
% 1.54/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f307,plain,(
% 1.54/0.56    sK1 = k2_relset_1(sK2,sK1,sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_2(sK3,sK1,sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(resolution,[],[f78,f54])).
% 1.54/0.56  fof(f54,plain,(
% 1.54/0.56    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f78,plain,(
% 1.54/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f31])).
% 1.54/0.56  fof(f31,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.56    inference(flattening,[],[f30])).
% 1.54/0.56  fof(f30,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f13])).
% 1.54/0.56  fof(f13,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.54/0.56  fof(f108,plain,(
% 1.54/0.56    k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4)),
% 1.54/0.56    inference(resolution,[],[f68,f52])).
% 1.54/0.56  fof(f68,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f25])).
% 1.54/0.56  fof(f25,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(ennf_transformation,[],[f6])).
% 1.54/0.56  fof(f6,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.54/0.56  fof(f1239,plain,(
% 1.54/0.56    sK1 != k2_relat_1(sK4) | k2_funct_1(sK3) = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f1238])).
% 1.54/0.56  fof(f1238,plain,(
% 1.54/0.56    k6_partfun1(sK2) != k6_partfun1(sK2) | sK1 != k2_relat_1(sK4) | k2_funct_1(sK3) = sK4 | ~v1_funct_1(sK4) | ~v1_relat_1(sK4) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(superposition,[],[f198,f1212])).
% 1.54/0.56  fof(f1212,plain,(
% 1.54/0.56    k6_partfun1(sK2) = k5_relat_1(sK4,sK3) | (~spl5_9 | ~spl5_24)),
% 1.54/0.56    inference(backward_demodulation,[],[f282,f1209])).
% 1.54/0.56  fof(f1209,plain,(
% 1.54/0.56    sK3 = k2_funct_1(sK4) | ~spl5_24),
% 1.54/0.56    inference(subsumption_resolution,[],[f1208,f110])).
% 1.54/0.56  fof(f110,plain,(
% 1.54/0.56    sK2 = k2_relat_1(sK3)),
% 1.54/0.56    inference(forward_demodulation,[],[f107,f53])).
% 1.54/0.56  fof(f53,plain,(
% 1.54/0.56    sK2 = k2_relset_1(sK1,sK2,sK3)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f107,plain,(
% 1.54/0.56    k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3)),
% 1.54/0.56    inference(resolution,[],[f68,f49])).
% 1.54/0.56  fof(f1208,plain,(
% 1.54/0.56    sK3 = k2_funct_1(sK4) | sK2 != k2_relat_1(sK3) | ~spl5_24),
% 1.54/0.56    inference(subsumption_resolution,[],[f1207,f47])).
% 1.54/0.56  fof(f1207,plain,(
% 1.54/0.56    ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK4) | sK2 != k2_relat_1(sK3) | ~spl5_24),
% 1.54/0.56    inference(subsumption_resolution,[],[f1206,f95])).
% 1.54/0.56  fof(f95,plain,(
% 1.54/0.56    v1_relat_1(sK3)),
% 1.54/0.56    inference(resolution,[],[f66,f49])).
% 1.54/0.56  fof(f1206,plain,(
% 1.54/0.56    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK4) | sK2 != k2_relat_1(sK3) | ~spl5_24),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f1204])).
% 1.54/0.56  fof(f1204,plain,(
% 1.54/0.56    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(sK4) | sK2 != k2_relat_1(sK3) | ~spl5_24),
% 1.54/0.56    inference(superposition,[],[f639,f459])).
% 1.54/0.56  fof(f459,plain,(
% 1.54/0.56    k6_partfun1(sK1) = k5_relat_1(sK3,sK4)),
% 1.54/0.56    inference(global_subsumption,[],[f453,f458])).
% 1.54/0.56  fof(f458,plain,(
% 1.54/0.56    k6_partfun1(sK1) = k5_relat_1(sK3,sK4) | ~m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.54/0.56    inference(resolution,[],[f441,f189])).
% 1.54/0.56  fof(f189,plain,(
% 1.54/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_partfun1(X2)) | k6_partfun1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.54/0.56    inference(resolution,[],[f79,f84])).
% 1.54/0.56  fof(f84,plain,(
% 1.54/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f60,f59])).
% 1.54/0.56  fof(f59,plain,(
% 1.54/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f12])).
% 1.54/0.56  fof(f12,axiom,(
% 1.54/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.54/0.56  fof(f60,plain,(
% 1.54/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f8])).
% 1.54/0.56  fof(f8,axiom,(
% 1.54/0.56    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 1.54/0.56  fof(f79,plain,(
% 1.54/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f46])).
% 1.54/0.56  fof(f46,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(nnf_transformation,[],[f33])).
% 1.54/0.56  fof(f33,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(flattening,[],[f32])).
% 1.54/0.56  fof(f32,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.54/0.56    inference(ennf_transformation,[],[f7])).
% 1.54/0.56  fof(f7,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.54/0.56  fof(f441,plain,(
% 1.54/0.56    r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1))),
% 1.54/0.56    inference(backward_demodulation,[],[f54,f380])).
% 1.54/0.56  fof(f380,plain,(
% 1.54/0.56    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f376,f47])).
% 1.54/0.56  fof(f376,plain,(
% 1.54/0.56    k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) | ~v1_funct_1(sK3)),
% 1.54/0.56    inference(resolution,[],[f205,f49])).
% 1.54/0.56  fof(f205,plain,(
% 1.54/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(X5)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f202,f50])).
% 1.54/0.56  fof(f202,plain,(
% 1.54/0.56    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK2,sK1,X5,sK4) = k5_relat_1(X5,sK4) | ~v1_funct_1(sK4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 1.54/0.56    inference(resolution,[],[f81,f52])).
% 1.54/0.56  fof(f81,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f35])).
% 1.54/0.56  fof(f35,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.56    inference(flattening,[],[f34])).
% 1.54/0.56  fof(f34,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.56    inference(ennf_transformation,[],[f11])).
% 1.54/0.56  fof(f11,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.54/0.56  fof(f453,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.54/0.56    inference(subsumption_resolution,[],[f452,f47])).
% 1.54/0.56  fof(f452,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3)),
% 1.54/0.56    inference(subsumption_resolution,[],[f451,f49])).
% 1.54/0.56  fof(f451,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.54/0.56    inference(subsumption_resolution,[],[f450,f50])).
% 1.54/0.56  fof(f450,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.54/0.56    inference(subsumption_resolution,[],[f443,f52])).
% 1.54/0.56  fof(f443,plain,(
% 1.54/0.56    m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) | ~v1_funct_1(sK3)),
% 1.54/0.56    inference(superposition,[],[f83,f380])).
% 1.54/0.56  fof(f83,plain,(
% 1.54/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f37])).
% 1.54/0.56  fof(f37,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.54/0.56    inference(flattening,[],[f36])).
% 1.54/0.56  fof(f36,plain,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.54/0.56    inference(ennf_transformation,[],[f10])).
% 1.54/0.56  fof(f10,axiom,(
% 1.54/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.54/0.56  fof(f639,plain,(
% 1.54/0.56    ( ! [X0] : (k6_partfun1(sK1) != k5_relat_1(X0,sK4) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(sK4) = X0 | k2_relat_1(X0) != sK2) ) | ~spl5_24),
% 1.54/0.56    inference(avatar_component_clause,[],[f638])).
% 1.54/0.56  fof(f638,plain,(
% 1.54/0.56    spl5_24 <=> ! [X0] : (k2_relat_1(X0) != sK2 | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(sK4) = X0 | k6_partfun1(sK1) != k5_relat_1(X0,sK4))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.54/0.56  fof(f282,plain,(
% 1.54/0.56    k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~spl5_9),
% 1.54/0.56    inference(avatar_component_clause,[],[f280])).
% 1.54/0.56  fof(f280,plain,(
% 1.54/0.56    spl5_9 <=> k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.54/0.56  fof(f198,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_partfun1(sK2) | k2_relat_1(X0) != sK1 | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f197,f138])).
% 1.54/0.56  fof(f138,plain,(
% 1.54/0.56    sK1 = k1_relat_1(sK3)),
% 1.54/0.56    inference(backward_demodulation,[],[f104,f130])).
% 1.54/0.56  fof(f130,plain,(
% 1.54/0.56    sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.54/0.56    inference(subsumption_resolution,[],[f129,f57])).
% 1.54/0.56  fof(f57,plain,(
% 1.54/0.56    k1_xboole_0 != sK2),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f129,plain,(
% 1.54/0.56    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.54/0.56    inference(subsumption_resolution,[],[f126,f48])).
% 1.54/0.56  fof(f126,plain,(
% 1.54/0.56    ~v1_funct_2(sK3,sK1,sK2) | k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK3)),
% 1.54/0.56    inference(resolution,[],[f69,f98])).
% 1.54/0.56  fof(f98,plain,(
% 1.54/0.56    sP0(sK1,sK3,sK2)),
% 1.54/0.56    inference(resolution,[],[f73,f49])).
% 1.54/0.56  fof(f73,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP0(X0,X2,X1)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f45])).
% 1.54/0.56  fof(f45,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(nnf_transformation,[],[f39])).
% 1.54/0.56  fof(f39,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & sP0(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(definition_folding,[],[f27,f38])).
% 1.54/0.56  fof(f38,plain,(
% 1.54/0.56    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.54/0.56  fof(f27,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(flattening,[],[f26])).
% 1.54/0.56  fof(f26,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(ennf_transformation,[],[f9])).
% 1.54/0.56  fof(f9,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.54/0.56  fof(f69,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | ~v1_funct_2(X1,X0,X2) | k1_xboole_0 = X2 | k1_relset_1(X0,X2,X1) = X0) )),
% 1.54/0.56    inference(cnf_transformation,[],[f44])).
% 1.54/0.56  fof(f44,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X2) | ~sP0(X0,X1,X2))),
% 1.54/0.56    inference(rectify,[],[f43])).
% 1.54/0.56  fof(f43,plain,(
% 1.54/0.56    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP0(X0,X2,X1))),
% 1.54/0.56    inference(nnf_transformation,[],[f38])).
% 1.54/0.56  fof(f104,plain,(
% 1.54/0.56    k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3)),
% 1.54/0.56    inference(resolution,[],[f67,f49])).
% 1.54/0.56  fof(f67,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f24])).
% 1.54/0.56  fof(f24,plain,(
% 1.54/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.54/0.56    inference(ennf_transformation,[],[f5])).
% 1.54/0.56  fof(f5,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.54/0.56  fof(f197,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_partfun1(sK2) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f196,f95])).
% 1.54/0.56  fof(f196,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_partfun1(sK2) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK3)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f195,f47])).
% 1.54/0.56  fof(f195,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_partfun1(sK2) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f194,f55])).
% 1.54/0.56  fof(f55,plain,(
% 1.54/0.56    v2_funct_1(sK3)),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f194,plain,(
% 1.54/0.56    ( ! [X0] : (k5_relat_1(X0,sK3) != k6_partfun1(sK2) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3) | ~v2_funct_1(sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.54/0.56    inference(superposition,[],[f87,f110])).
% 1.54/0.56  fof(f87,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(definition_unfolding,[],[f63,f59])).
% 1.54/0.56  fof(f63,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f20])).
% 1.54/0.56  fof(f20,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f19])).
% 1.54/0.56  fof(f19,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f3])).
% 1.54/0.56  fof(f3,axiom,(
% 1.54/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.54/0.56  fof(f640,plain,(
% 1.54/0.56    ~spl5_3 | spl5_24),
% 1.54/0.56    inference(avatar_split_clause,[],[f636,f638,f158])).
% 1.54/0.56  fof(f158,plain,(
% 1.54/0.56    spl5_3 <=> v2_funct_1(sK4)),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.54/0.56  fof(f636,plain,(
% 1.54/0.56    ( ! [X0] : (k2_relat_1(X0) != sK2 | k6_partfun1(sK1) != k5_relat_1(X0,sK4) | k2_funct_1(sK4) = X0 | ~v2_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(forward_demodulation,[],[f635,f141])).
% 1.54/0.56  fof(f141,plain,(
% 1.54/0.56    sK2 = k1_relat_1(sK4)),
% 1.54/0.56    inference(backward_demodulation,[],[f105,f132])).
% 1.54/0.56  fof(f132,plain,(
% 1.54/0.56    sK2 = k1_relset_1(sK2,sK1,sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f131,f56])).
% 1.54/0.56  fof(f56,plain,(
% 1.54/0.56    k1_xboole_0 != sK1),
% 1.54/0.56    inference(cnf_transformation,[],[f42])).
% 1.54/0.56  fof(f131,plain,(
% 1.54/0.56    k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f127,f51])).
% 1.54/0.56  fof(f127,plain,(
% 1.54/0.56    ~v1_funct_2(sK4,sK2,sK1) | k1_xboole_0 = sK1 | sK2 = k1_relset_1(sK2,sK1,sK4)),
% 1.54/0.56    inference(resolution,[],[f69,f99])).
% 1.54/0.56  fof(f99,plain,(
% 1.54/0.56    sP0(sK2,sK4,sK1)),
% 1.54/0.56    inference(resolution,[],[f73,f52])).
% 1.54/0.56  fof(f105,plain,(
% 1.54/0.56    k1_relset_1(sK2,sK1,sK4) = k1_relat_1(sK4)),
% 1.54/0.56    inference(resolution,[],[f67,f52])).
% 1.54/0.56  fof(f635,plain,(
% 1.54/0.56    ( ! [X0] : (k6_partfun1(sK1) != k5_relat_1(X0,sK4) | k2_funct_1(sK4) = X0 | k2_relat_1(X0) != k1_relat_1(sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f634,f96])).
% 1.54/0.56  fof(f634,plain,(
% 1.54/0.56    ( ! [X0] : (k6_partfun1(sK1) != k5_relat_1(X0,sK4) | k2_funct_1(sK4) = X0 | k2_relat_1(X0) != k1_relat_1(sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK4)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f354,f50])).
% 1.54/0.56  fof(f354,plain,(
% 1.54/0.56    ( ! [X0] : (k6_partfun1(sK1) != k5_relat_1(X0,sK4) | k2_funct_1(sK4) = X0 | k2_relat_1(X0) != k1_relat_1(sK4) | ~v2_funct_1(sK4) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.54/0.56    inference(superposition,[],[f87,f314])).
% 1.54/0.56  fof(f620,plain,(
% 1.54/0.56    ~spl5_4),
% 1.54/0.56    inference(avatar_contradiction_clause,[],[f619])).
% 1.54/0.56  fof(f619,plain,(
% 1.54/0.56    $false | ~spl5_4),
% 1.54/0.56    inference(subsumption_resolution,[],[f618,f85])).
% 1.54/0.56  fof(f85,plain,(
% 1.54/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.54/0.56    inference(definition_unfolding,[],[f62,f59])).
% 1.54/0.56  fof(f62,plain,(
% 1.54/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.54/0.56    inference(cnf_transformation,[],[f1])).
% 1.54/0.56  fof(f1,axiom,(
% 1.54/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.54/0.56  fof(f618,plain,(
% 1.54/0.56    ~v2_funct_1(k6_partfun1(sK1)) | ~spl5_4),
% 1.54/0.56    inference(forward_demodulation,[],[f617,f459])).
% 1.54/0.56  fof(f617,plain,(
% 1.54/0.56    ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_4),
% 1.54/0.56    inference(subsumption_resolution,[],[f616,f47])).
% 1.54/0.56  fof(f616,plain,(
% 1.54/0.56    ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_4),
% 1.54/0.56    inference(subsumption_resolution,[],[f615,f95])).
% 1.54/0.56  fof(f615,plain,(
% 1.54/0.56    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_4),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f613])).
% 1.54/0.56  fof(f613,plain,(
% 1.54/0.56    sK2 != sK2 | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v2_funct_1(k5_relat_1(sK3,sK4)) | ~spl5_4),
% 1.54/0.56    inference(superposition,[],[f163,f110])).
% 1.54/0.56  fof(f163,plain,(
% 1.54/0.56    ( ! [X1] : (k2_relat_1(X1) != sK2 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK4))) ) | ~spl5_4),
% 1.54/0.56    inference(avatar_component_clause,[],[f162])).
% 1.54/0.56  fof(f162,plain,(
% 1.54/0.56    spl5_4 <=> ! [X1] : (k2_relat_1(X1) != sK2 | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(k5_relat_1(X1,sK4)))),
% 1.54/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.54/0.56  fof(f347,plain,(
% 1.54/0.56    spl5_9 | ~spl5_3),
% 1.54/0.56    inference(avatar_split_clause,[],[f346,f158,f280])).
% 1.54/0.56  fof(f346,plain,(
% 1.54/0.56    ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))),
% 1.54/0.56    inference(global_subsumption,[],[f333])).
% 1.54/0.56  fof(f333,plain,(
% 1.54/0.56    ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4))),
% 1.54/0.56    inference(subsumption_resolution,[],[f332,f50])).
% 1.54/0.56  fof(f332,plain,(
% 1.54/0.56    ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f331,f51])).
% 1.54/0.56  fof(f331,plain,(
% 1.54/0.56    ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f326,f52])).
% 1.54/0.56  fof(f326,plain,(
% 1.54/0.56    ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(subsumption_resolution,[],[f317,f56])).
% 1.54/0.56  fof(f317,plain,(
% 1.54/0.56    k1_xboole_0 = sK1 | ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(trivial_inequality_removal,[],[f316])).
% 1.54/0.56  fof(f316,plain,(
% 1.54/0.56    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK4) | k6_partfun1(sK2) = k5_relat_1(sK4,k2_funct_1(sK4)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4)),
% 1.54/0.56    inference(superposition,[],[f76,f313])).
% 1.54/0.56  fof(f76,plain,(
% 1.54/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f29])).
% 1.54/0.56  fof(f29,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.54/0.56    inference(flattening,[],[f28])).
% 1.54/0.56  fof(f28,plain,(
% 1.54/0.56    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.54/0.56    inference(ennf_transformation,[],[f14])).
% 1.54/0.56  fof(f14,axiom,(
% 1.54/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.54/0.56  fof(f164,plain,(
% 1.54/0.56    spl5_3 | spl5_4),
% 1.54/0.56    inference(avatar_split_clause,[],[f156,f162,f158])).
% 1.54/0.56  fof(f156,plain,(
% 1.54/0.56    ( ! [X1] : (k2_relat_1(X1) != sK2 | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X1,sK4)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f155,f96])).
% 1.54/0.56  fof(f155,plain,(
% 1.54/0.56    ( ! [X1] : (k2_relat_1(X1) != sK2 | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X1,sK4)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK4)) )),
% 1.54/0.56    inference(subsumption_resolution,[],[f154,f50])).
% 1.54/0.56  fof(f154,plain,(
% 1.54/0.56    ( ! [X1] : (k2_relat_1(X1) != sK2 | v2_funct_1(sK4) | ~v2_funct_1(k5_relat_1(X1,sK4)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(sK4) | ~v1_relat_1(sK4)) )),
% 1.54/0.56    inference(superposition,[],[f65,f141])).
% 1.54/0.56  fof(f65,plain,(
% 1.54/0.56    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.54/0.56    inference(cnf_transformation,[],[f22])).
% 1.54/0.56  fof(f22,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.54/0.56    inference(flattening,[],[f21])).
% 1.54/0.56  fof(f21,plain,(
% 1.54/0.56    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.54/0.56    inference(ennf_transformation,[],[f2])).
% 1.54/0.56  fof(f2,axiom,(
% 1.54/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.54/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.54/0.56  % SZS output end Proof for theBenchmark
% 1.54/0.56  % (4391)------------------------------
% 1.54/0.56  % (4391)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.56  % (4391)Termination reason: Refutation
% 1.54/0.56  
% 1.54/0.56  % (4391)Memory used [KB]: 11641
% 1.54/0.56  % (4391)Time elapsed: 0.141 s
% 1.54/0.56  % (4391)------------------------------
% 1.54/0.56  % (4391)------------------------------
% 1.54/0.57  % (4384)Success in time 0.21 s
%------------------------------------------------------------------------------
