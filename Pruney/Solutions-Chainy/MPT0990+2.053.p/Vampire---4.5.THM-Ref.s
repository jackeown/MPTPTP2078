%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:37 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 494 expanded)
%              Number of leaves         :   12 (  88 expanded)
%              Depth                    :   22
%              Number of atoms          :  419 (3807 expanded)
%              Number of equality atoms :  144 (1249 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f997,plain,(
    $false ),
    inference(subsumption_resolution,[],[f996,f131])).

fof(f131,plain,(
    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f130,f36])).

fof(f36,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f130,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f129,f38])).

fof(f38,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f129,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f128,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f42,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f43,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f43,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f996,plain,(
    ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f995,f127])).

fof(f127,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f126,f36])).

fof(f126,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f124,f44])).

fof(f124,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f120,f42])).

fof(f120,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f43,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f995,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f994,f44])).

fof(f994,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f993,f42])).

fof(f993,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f991,f924])).

fof(f924,plain,(
    ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f923,f522])).

fof(f522,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f521,f436])).

fof(f436,plain,(
    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f435,f41])).

fof(f41,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f435,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f434,f165])).

fof(f165,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f149,f118])).

fof(f118,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f117,f39])).

fof(f39,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f15])).

fof(f117,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_xboole_0 = sK0
    | sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f34,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f34,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f149,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f434,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f431,f148])).

fof(f148,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f35,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f431,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | ~ v1_relat_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | sK3 = k2_funct_1(sK2) ),
    inference(resolution,[],[f205,f33])).

fof(f33,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f205,plain,(
    ! [X6] :
      ( ~ v1_funct_1(X6)
      | k6_relat_1(sK0) != k5_relat_1(sK2,X6)
      | ~ v1_relat_1(X6)
      | sK1 != k1_relat_1(X6)
      | k2_funct_1(sK2) = X6 ) ),
    inference(backward_demodulation,[],[f203,f204])).

fof(f204,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f184,f36])).

fof(f184,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f203,plain,(
    ! [X6] :
      ( k6_relat_1(sK0) != k5_relat_1(sK2,X6)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | k2_funct_1(sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f201,f182])).

fof(f182,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f44,f49])).

fof(f201,plain,(
    ! [X6] :
      ( k6_relat_1(sK0) != k5_relat_1(sK2,X6)
      | ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | k2_funct_1(sK2) = X6 ) ),
    inference(backward_demodulation,[],[f93,f199])).

fof(f199,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f183,f133])).

fof(f133,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f132,f40])).

fof(f40,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f43,f57])).

fof(f183,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2) ),
    inference(resolution,[],[f44,f50])).

% (2244)Refutation not found, incomplete strategy% (2244)------------------------------
% (2244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2244)Termination reason: Refutation not found, incomplete strategy

% (2244)Memory used [KB]: 10746
% (2244)Time elapsed: 0.210 s
% (2244)------------------------------
% (2244)------------------------------
fof(f93,plain,(
    ! [X6] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X6)
      | k2_funct_1(sK2) = X6 ) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,(
    ! [X6] :
      ( ~ v1_relat_1(sK2)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(X6)
      | ~ v1_funct_1(X6)
      | k2_relat_1(sK2) != k1_relat_1(X6)
      | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X6)
      | k2_funct_1(sK2) = X6 ) ),
    inference(resolution,[],[f38,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k1_relat_1(X1)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k2_funct_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
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
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).

fof(f521,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f518,f516])).

fof(f516,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f507,f42])).

fof(f507,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f169,f44])).

fof(f169,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f159,f33])).

fof(f159,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(resolution,[],[f35,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
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
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f518,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f218,f516])).

fof(f218,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(resolution,[],[f66,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f45,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f37,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f923,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f922,f35])).

fof(f922,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f921,f33])).

fof(f921,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f920,f44])).

fof(f920,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f919,f42])).

fof(f919,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f65,f516])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f991,plain,
    ( m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f65,f744])).

fof(f744,plain,(
    k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    inference(forward_demodulation,[],[f743,f202])).

fof(f202,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f200,f182])).

fof(f200,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f94,f199])).

fof(f94,plain,
    ( ~ v1_relat_1(sK2)
    | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f91,f42])).

fof(f91,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f38,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f743,plain,(
    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f737,f127])).

fof(f737,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f208,f131])).

fof(f208,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k1_partfun1(sK0,sK1,X3,X4,sK2,X2) = k5_relat_1(sK2,X2) ) ),
    inference(subsumption_resolution,[],[f192,f42])).

fof(f192,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(sK2)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(sK0,sK1,X3,X4,sK2,X2) = k5_relat_1(sK2,X2) ) ),
    inference(resolution,[],[f44,f63])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (2232)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (2240)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (2256)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (2248)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.33/0.56  % (2228)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.33/0.57  % (2233)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.66/0.57  % (2245)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.66/0.58  % (2237)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.66/0.58  % (2234)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.58  % (2230)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.66/0.58  % (2256)Refutation not found, incomplete strategy% (2256)------------------------------
% 1.66/0.58  % (2256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (2257)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.66/0.58  % (2256)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (2256)Memory used [KB]: 11001
% 1.66/0.58  % (2256)Time elapsed: 0.146 s
% 1.66/0.58  % (2256)------------------------------
% 1.66/0.58  % (2256)------------------------------
% 1.66/0.59  % (2236)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.66/0.59  % (2241)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.66/0.59  % (2231)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.66/0.59  % (2249)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.66/0.60  % (2229)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.66/0.60  % (2251)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.66/0.60  % (2254)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.66/0.60  % (2242)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.66/0.60  % (2253)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.66/0.60  % (2252)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.66/0.60  % (2247)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.61  % (2246)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.66/0.61  % (2235)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.66/0.61  % (2255)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.66/0.61  % (2245)Refutation found. Thanks to Tanya!
% 1.66/0.61  % SZS status Theorem for theBenchmark
% 1.66/0.61  % (2243)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.66/0.61  % (2244)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.66/0.61  % (2250)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.66/0.61  % (2238)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.66/0.63  % (2239)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.66/0.63  % SZS output start Proof for theBenchmark
% 1.66/0.63  fof(f997,plain,(
% 1.66/0.63    $false),
% 1.66/0.63    inference(subsumption_resolution,[],[f996,f131])).
% 1.66/0.63  fof(f131,plain,(
% 1.66/0.63    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f130,f36])).
% 1.66/0.63  fof(f36,plain,(
% 1.66/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f15,plain,(
% 1.66/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.66/0.63    inference(flattening,[],[f14])).
% 1.66/0.63  fof(f14,plain,(
% 1.66/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.66/0.63    inference(ennf_transformation,[],[f13])).
% 1.66/0.63  fof(f13,negated_conjecture,(
% 1.66/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.66/0.63    inference(negated_conjecture,[],[f12])).
% 1.66/0.63  fof(f12,conjecture,(
% 1.66/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.66/0.63  fof(f130,plain,(
% 1.66/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f129,f38])).
% 1.66/0.63  fof(f38,plain,(
% 1.66/0.63    v2_funct_1(sK2)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f129,plain,(
% 1.66/0.63    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f128,f44])).
% 1.66/0.63  fof(f44,plain,(
% 1.66/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f128,plain,(
% 1.66/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f122,f42])).
% 1.66/0.63  fof(f42,plain,(
% 1.66/0.63    v1_funct_1(sK2)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f122,plain,(
% 1.66/0.63    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(resolution,[],[f43,f60])).
% 1.66/0.63  fof(f60,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.66/0.63    inference(cnf_transformation,[],[f26])).
% 1.66/0.63  fof(f26,plain,(
% 1.66/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.66/0.63    inference(flattening,[],[f25])).
% 1.66/0.63  fof(f25,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.66/0.63    inference(ennf_transformation,[],[f11])).
% 1.66/0.63  fof(f11,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.66/0.63  fof(f43,plain,(
% 1.66/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f996,plain,(
% 1.66/0.63    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f995,f127])).
% 1.66/0.63  fof(f127,plain,(
% 1.66/0.63    v1_funct_1(k2_funct_1(sK2))),
% 1.66/0.63    inference(subsumption_resolution,[],[f126,f36])).
% 1.66/0.63  fof(f126,plain,(
% 1.66/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.66/0.63    inference(subsumption_resolution,[],[f125,f38])).
% 1.66/0.63  fof(f125,plain,(
% 1.66/0.63    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.66/0.63    inference(subsumption_resolution,[],[f124,f44])).
% 1.66/0.63  fof(f124,plain,(
% 1.66/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.66/0.63    inference(subsumption_resolution,[],[f120,f42])).
% 1.66/0.63  fof(f120,plain,(
% 1.66/0.63    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 1.66/0.63    inference(resolution,[],[f43,f58])).
% 1.66/0.63  fof(f58,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 1.66/0.63    inference(cnf_transformation,[],[f26])).
% 1.66/0.63  fof(f995,plain,(
% 1.66/0.63    ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f994,f44])).
% 1.66/0.63  fof(f994,plain,(
% 1.66/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f993,f42])).
% 1.66/0.63  fof(f993,plain,(
% 1.66/0.63    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f991,f924])).
% 1.66/0.63  fof(f924,plain,(
% 1.66/0.63    ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.63    inference(resolution,[],[f923,f522])).
% 1.66/0.63  fof(f522,plain,(
% 1.66/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.63    inference(subsumption_resolution,[],[f521,f436])).
% 1.66/0.63  fof(f436,plain,(
% 1.66/0.63    k6_relat_1(sK0) != k5_relat_1(sK2,sK3)),
% 1.66/0.63    inference(subsumption_resolution,[],[f435,f41])).
% 1.66/0.63  fof(f41,plain,(
% 1.66/0.63    sK3 != k2_funct_1(sK2)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f435,plain,(
% 1.66/0.63    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | sK3 = k2_funct_1(sK2)),
% 1.66/0.63    inference(subsumption_resolution,[],[f434,f165])).
% 1.66/0.63  fof(f165,plain,(
% 1.66/0.63    sK1 = k1_relat_1(sK3)),
% 1.66/0.63    inference(forward_demodulation,[],[f149,f118])).
% 1.66/0.63  fof(f118,plain,(
% 1.66/0.63    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.66/0.63    inference(subsumption_resolution,[],[f117,f39])).
% 1.66/0.63  fof(f39,plain,(
% 1.66/0.63    k1_xboole_0 != sK0),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f117,plain,(
% 1.66/0.63    k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.66/0.63    inference(subsumption_resolution,[],[f112,f35])).
% 1.66/0.63  fof(f35,plain,(
% 1.66/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f112,plain,(
% 1.66/0.63    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | k1_xboole_0 = sK0 | sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.66/0.63    inference(resolution,[],[f34,f57])).
% 1.66/0.63  fof(f57,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f24])).
% 1.66/0.63  fof(f24,plain,(
% 1.66/0.63    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.63    inference(flattening,[],[f23])).
% 1.66/0.63  fof(f23,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.63    inference(ennf_transformation,[],[f7])).
% 1.66/0.63  fof(f7,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.66/0.63  fof(f34,plain,(
% 1.66/0.63    v1_funct_2(sK3,sK1,sK0)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f149,plain,(
% 1.66/0.63    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 1.66/0.63    inference(resolution,[],[f35,f50])).
% 1.66/0.63  fof(f50,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f21])).
% 1.66/0.63  fof(f21,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.63    inference(ennf_transformation,[],[f4])).
% 1.66/0.63  fof(f4,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.66/0.63  fof(f434,plain,(
% 1.66/0.63    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2)),
% 1.66/0.63    inference(subsumption_resolution,[],[f431,f148])).
% 1.66/0.63  fof(f148,plain,(
% 1.66/0.63    v1_relat_1(sK3)),
% 1.66/0.63    inference(resolution,[],[f35,f49])).
% 1.66/0.63  fof(f49,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f20])).
% 1.66/0.63  fof(f20,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.63    inference(ennf_transformation,[],[f3])).
% 1.66/0.63  fof(f3,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.63  fof(f431,plain,(
% 1.66/0.63    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | ~v1_relat_1(sK3) | sK1 != k1_relat_1(sK3) | sK3 = k2_funct_1(sK2)),
% 1.66/0.63    inference(resolution,[],[f205,f33])).
% 1.66/0.63  fof(f33,plain,(
% 1.66/0.63    v1_funct_1(sK3)),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f205,plain,(
% 1.66/0.63    ( ! [X6] : (~v1_funct_1(X6) | k6_relat_1(sK0) != k5_relat_1(sK2,X6) | ~v1_relat_1(X6) | sK1 != k1_relat_1(X6) | k2_funct_1(sK2) = X6) )),
% 1.66/0.63    inference(backward_demodulation,[],[f203,f204])).
% 1.66/0.63  fof(f204,plain,(
% 1.66/0.63    sK1 = k2_relat_1(sK2)),
% 1.66/0.63    inference(forward_demodulation,[],[f184,f36])).
% 1.66/0.63  fof(f184,plain,(
% 1.66/0.63    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.66/0.63    inference(resolution,[],[f44,f51])).
% 1.66/0.63  fof(f51,plain,(
% 1.66/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.66/0.63    inference(cnf_transformation,[],[f22])).
% 1.66/0.63  fof(f22,plain,(
% 1.66/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.63    inference(ennf_transformation,[],[f5])).
% 1.66/0.63  fof(f5,axiom,(
% 1.66/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.66/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.66/0.63  fof(f203,plain,(
% 1.66/0.63    ( ! [X6] : (k6_relat_1(sK0) != k5_relat_1(sK2,X6) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k2_relat_1(sK2) != k1_relat_1(X6) | k2_funct_1(sK2) = X6) )),
% 1.66/0.63    inference(subsumption_resolution,[],[f201,f182])).
% 1.66/0.63  fof(f182,plain,(
% 1.66/0.63    v1_relat_1(sK2)),
% 1.66/0.63    inference(resolution,[],[f44,f49])).
% 1.66/0.63  fof(f201,plain,(
% 1.66/0.63    ( ! [X6] : (k6_relat_1(sK0) != k5_relat_1(sK2,X6) | ~v1_relat_1(sK2) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k2_relat_1(sK2) != k1_relat_1(X6) | k2_funct_1(sK2) = X6) )),
% 1.66/0.63    inference(backward_demodulation,[],[f93,f199])).
% 1.66/0.63  fof(f199,plain,(
% 1.66/0.63    sK0 = k1_relat_1(sK2)),
% 1.66/0.63    inference(forward_demodulation,[],[f183,f133])).
% 1.66/0.63  fof(f133,plain,(
% 1.66/0.63    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.63    inference(subsumption_resolution,[],[f132,f40])).
% 1.66/0.63  fof(f40,plain,(
% 1.66/0.63    k1_xboole_0 != sK1),
% 1.66/0.63    inference(cnf_transformation,[],[f15])).
% 1.66/0.63  fof(f132,plain,(
% 1.66/0.63    k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.63    inference(subsumption_resolution,[],[f123,f44])).
% 1.66/0.63  fof(f123,plain,(
% 1.66/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.63    inference(resolution,[],[f43,f57])).
% 1.66/0.63  fof(f183,plain,(
% 1.66/0.63    k1_relat_1(sK2) = k1_relset_1(sK0,sK1,sK2)),
% 1.66/0.63    inference(resolution,[],[f44,f50])).
% 1.66/0.64  % (2244)Refutation not found, incomplete strategy% (2244)------------------------------
% 1.66/0.64  % (2244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.64  % (2244)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.64  
% 1.66/0.64  % (2244)Memory used [KB]: 10746
% 1.66/0.64  % (2244)Time elapsed: 0.210 s
% 1.66/0.64  % (2244)------------------------------
% 1.66/0.64  % (2244)------------------------------
% 1.66/0.64  fof(f93,plain,(
% 1.66/0.64    ( ! [X6] : (~v1_relat_1(sK2) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k2_relat_1(sK2) != k1_relat_1(X6) | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X6) | k2_funct_1(sK2) = X6) )),
% 1.66/0.64    inference(subsumption_resolution,[],[f90,f42])).
% 1.66/0.64  fof(f90,plain,(
% 1.66/0.64    ( ! [X6] : (~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(X6) | ~v1_funct_1(X6) | k2_relat_1(sK2) != k1_relat_1(X6) | k6_relat_1(k1_relat_1(sK2)) != k5_relat_1(sK2,X6) | k2_funct_1(sK2) = X6) )),
% 1.66/0.64    inference(resolution,[],[f38,f48])).
% 1.66/0.64  fof(f48,plain,(
% 1.66/0.64    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X0) | k2_relat_1(X0) != k1_relat_1(X1) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_funct_1(X0) = X1) )),
% 1.66/0.64    inference(cnf_transformation,[],[f19])).
% 1.66/0.64  fof(f19,plain,(
% 1.66/0.64    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.64    inference(flattening,[],[f18])).
% 1.66/0.64  fof(f18,plain,(
% 1.66/0.64    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.66/0.64    inference(ennf_transformation,[],[f2])).
% 1.66/0.64  fof(f2,axiom,(
% 1.66/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_funct_1)).
% 1.66/0.64  fof(f521,plain,(
% 1.66/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.64    inference(forward_demodulation,[],[f518,f516])).
% 1.66/0.64  fof(f516,plain,(
% 1.66/0.64    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.66/0.64    inference(subsumption_resolution,[],[f507,f42])).
% 1.66/0.64  fof(f507,plain,(
% 1.66/0.64    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.66/0.64    inference(resolution,[],[f169,f44])).
% 1.66/0.64  fof(f169,plain,(
% 1.66/0.64    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.66/0.64    inference(subsumption_resolution,[],[f159,f33])).
% 1.66/0.64  fof(f159,plain,(
% 1.66/0.64    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.66/0.64    inference(resolution,[],[f35,f63])).
% 1.66/0.64  fof(f63,plain,(
% 1.66/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.66/0.64    inference(cnf_transformation,[],[f30])).
% 1.66/0.64  fof(f30,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.66/0.64    inference(flattening,[],[f29])).
% 1.66/0.64  fof(f29,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.66/0.64    inference(ennf_transformation,[],[f9])).
% 1.66/0.64  fof(f9,axiom,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.66/0.64  fof(f518,plain,(
% 1.66/0.64    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.66/0.64    inference(backward_demodulation,[],[f218,f516])).
% 1.66/0.64  fof(f218,plain,(
% 1.66/0.64    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.66/0.64    inference(resolution,[],[f66,f62])).
% 1.66/0.64  fof(f62,plain,(
% 1.66/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.66/0.64    inference(cnf_transformation,[],[f28])).
% 1.66/0.64  fof(f28,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.64    inference(flattening,[],[f27])).
% 1.66/0.64  fof(f27,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.66/0.64    inference(ennf_transformation,[],[f6])).
% 1.66/0.64  fof(f6,axiom,(
% 1.66/0.64    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.66/0.64  fof(f66,plain,(
% 1.66/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.66/0.64    inference(definition_unfolding,[],[f37,f45])).
% 1.66/0.64  fof(f45,plain,(
% 1.66/0.64    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 1.66/0.64    inference(cnf_transformation,[],[f10])).
% 1.66/0.64  fof(f10,axiom,(
% 1.66/0.64    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.66/0.64  fof(f37,plain,(
% 1.66/0.64    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.66/0.64    inference(cnf_transformation,[],[f15])).
% 1.66/0.64  fof(f923,plain,(
% 1.66/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.66/0.64    inference(subsumption_resolution,[],[f922,f35])).
% 1.66/0.64  fof(f922,plain,(
% 1.66/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.64    inference(subsumption_resolution,[],[f921,f33])).
% 1.66/0.64  fof(f921,plain,(
% 1.66/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.64    inference(subsumption_resolution,[],[f920,f44])).
% 1.66/0.64  fof(f920,plain,(
% 1.66/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.64    inference(subsumption_resolution,[],[f919,f42])).
% 1.66/0.64  fof(f919,plain,(
% 1.66/0.64    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.64    inference(superposition,[],[f65,f516])).
% 1.66/0.64  fof(f65,plain,(
% 1.66/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.66/0.64    inference(cnf_transformation,[],[f32])).
% 1.66/0.64  fof(f32,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.66/0.64    inference(flattening,[],[f31])).
% 1.66/0.64  fof(f31,plain,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.66/0.64    inference(ennf_transformation,[],[f8])).
% 1.66/0.64  fof(f8,axiom,(
% 1.66/0.64    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.66/0.64  fof(f991,plain,(
% 1.66/0.64    m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.66/0.64    inference(superposition,[],[f65,f744])).
% 1.66/0.64  fof(f744,plain,(
% 1.66/0.64    k6_relat_1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(forward_demodulation,[],[f743,f202])).
% 1.66/0.64  fof(f202,plain,(
% 1.66/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(subsumption_resolution,[],[f200,f182])).
% 1.66/0.64  fof(f200,plain,(
% 1.66/0.64    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.66/0.64    inference(backward_demodulation,[],[f94,f199])).
% 1.66/0.64  fof(f94,plain,(
% 1.66/0.64    ~v1_relat_1(sK2) | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(subsumption_resolution,[],[f91,f42])).
% 1.66/0.64  fof(f91,plain,(
% 1.66/0.64    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k6_relat_1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(resolution,[],[f38,f46])).
% 1.66/0.64  fof(f46,plain,(
% 1.66/0.64    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) )),
% 1.66/0.64    inference(cnf_transformation,[],[f17])).
% 1.66/0.64  fof(f17,plain,(
% 1.66/0.64    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.66/0.64    inference(flattening,[],[f16])).
% 1.66/0.64  fof(f16,plain,(
% 1.66/0.64    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.66/0.64    inference(ennf_transformation,[],[f1])).
% 1.66/0.64  fof(f1,axiom,(
% 1.66/0.64    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 1.66/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 1.66/0.64  fof(f743,plain,(
% 1.66/0.64    k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(subsumption_resolution,[],[f737,f127])).
% 1.66/0.64  fof(f737,plain,(
% 1.66/0.64    ~v1_funct_1(k2_funct_1(sK2)) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2))),
% 1.66/0.64    inference(resolution,[],[f208,f131])).
% 1.66/0.64  fof(f208,plain,(
% 1.66/0.64    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k1_partfun1(sK0,sK1,X3,X4,sK2,X2) = k5_relat_1(sK2,X2)) )),
% 1.66/0.64    inference(subsumption_resolution,[],[f192,f42])).
% 1.66/0.64  fof(f192,plain,(
% 1.66/0.64    ( ! [X4,X2,X3] : (~v1_funct_1(sK2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(sK0,sK1,X3,X4,sK2,X2) = k5_relat_1(sK2,X2)) )),
% 1.66/0.64    inference(resolution,[],[f44,f63])).
% 1.66/0.64  % SZS output end Proof for theBenchmark
% 1.66/0.64  % (2245)------------------------------
% 1.66/0.64  % (2245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.64  % (2245)Termination reason: Refutation
% 1.66/0.64  
% 1.66/0.64  % (2245)Memory used [KB]: 2046
% 1.66/0.64  % (2245)Time elapsed: 0.181 s
% 1.66/0.64  % (2245)------------------------------
% 1.66/0.64  % (2245)------------------------------
% 1.66/0.64  % (2227)Success in time 0.281 s
%------------------------------------------------------------------------------
