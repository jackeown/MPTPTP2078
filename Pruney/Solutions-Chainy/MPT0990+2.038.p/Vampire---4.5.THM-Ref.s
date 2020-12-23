%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  148 (1473 expanded)
%              Number of leaves         :   17 ( 463 expanded)
%              Depth                    :   21
%              Number of atoms          :  606 (15338 expanded)
%              Number of equality atoms :  210 (5316 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f423,plain,(
    $false ),
    inference(subsumption_resolution,[],[f422,f416])).

fof(f416,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f408,f56])).

fof(f56,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f408,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f257,f385])).

fof(f385,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f220,f202])).

fof(f202,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f200,f198])).

fof(f198,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f195,f44])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f40,f39])).

fof(f39,plain,
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

fof(f40,plain,
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

fof(f195,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f149,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f149,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f146,f47])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f146,plain,(
    ! [X4,X5,X3] :
      ( k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f200,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f134,f198])).

fof(f134,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f133,f91])).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f133,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f76,f90])).

fof(f90,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f51,f57])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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

fof(f220,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f219,f198])).

fof(f219,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f216,f44])).

fof(f216,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f154,f46])).

fof(f154,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(X5) ) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0)))
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X5) ) ),
    inference(resolution,[],[f80,f49])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f257,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f256,f198])).

fof(f256,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f255,f44])).

fof(f255,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f254,f50])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f254,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f46])).

fof(f253,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f173,f45])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f173,plain,(
    ! [X2,X3] :
      ( ~ v1_funct_2(X3,X2,sK1)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f172,f47])).

fof(f172,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X2,X3] :
      ( sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(subsumption_resolution,[],[f170,f53])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f41])).

fof(f170,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK0
      | sK1 != k2_relset_1(X2,sK1,X3)
      | ~ v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | v2_funct_1(sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
      | ~ v1_funct_2(X3,X2,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(resolution,[],[f74,f48])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(X4,X1,X2)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v2_funct_1(X4)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

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
    inference(flattening,[],[f31])).

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

fof(f422,plain,(
    ~ v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f420,f273])).

fof(f273,plain,(
    k6_relat_1(sK1) != k5_relat_1(sK3,sK2) ),
    inference(trivial_inequality_removal,[],[f268])).

fof(f268,plain,
    ( sK0 != sK0
    | k6_relat_1(sK1) != k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f239,f263])).

fof(f263,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f103,f262])).

fof(f262,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f261,f201])).

fof(f201,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f90,f198])).

fof(f261,plain,
    ( ~ r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(forward_demodulation,[],[f260,f198])).

fof(f260,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f259,f47])).

fof(f259,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f258,f49])).

fof(f258,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f158,f48])).

fof(f158,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK1,sK0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f157,f44])).

fof(f157,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f155,f46])).

fof(f155,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f92,f45])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f71,f57])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
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

fof(f103,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f64,f49])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f239,plain,
    ( k6_relat_1(sK1) != k5_relat_1(sK3,sK2)
    | sK0 != k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f238,f105])).

fof(f105,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f102,f50])).

fof(f102,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f64,f46])).

fof(f238,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) ),
    inference(forward_demodulation,[],[f237,f123])).

fof(f123,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f99,f122])).

fof(f122,plain,(
    sK0 = k1_relset_1(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f121,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f119,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f41])).

fof(f119,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f237,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f236,f93])).

fof(f93,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f236,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f235,f55])).

fof(f55,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f41])).

fof(f235,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f232,f52])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f232,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK3)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = sK3
    | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f144,f44])).

fof(f144,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | k2_relat_1(sK3) != k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | sK3 = k2_funct_1(X1)
      | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f141,f94])).

fof(f94,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f62,f49])).

fof(f141,plain,(
    ! [X1] :
      ( k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1)
      | k2_relat_1(sK3) != k1_relat_1(X1)
      | ~ v2_funct_1(X1)
      | sK3 = k2_funct_1(X1)
      | ~ v1_relat_1(sK3)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f61,f47])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f420,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f128,f417])).

fof(f417,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f415,f416])).

fof(f415,plain,
    ( ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f409])).

fof(f409,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f266,f385])).

fof(f266,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f231,f263])).

fof(f231,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f230,f94])).

fof(f230,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f224,f127])).

fof(f127,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f100,f126])).

fof(f126,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f125,f49])).

fof(f125,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f120,f53])).

fof(f120,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f65,f48])).

fof(f100,plain,(
    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(resolution,[],[f63,f49])).

fof(f224,plain,
    ( k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f143,f47])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f142,f105])).

fof(f142,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f140,f93])).

fof(f140,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f61,f44])).

fof(f128,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1) ),
    inference(backward_demodulation,[],[f110,f127])).

fof(f110,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f107,f94])).

fof(f107,plain,
    ( ~ v2_funct_1(sK3)
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f59,f47])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (5017)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (5009)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (4994)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (5001)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (5005)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (4992)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (4998)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (4996)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (4993)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.53  % (5002)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (4991)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (5015)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (5012)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (4997)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (5019)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (5007)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (5007)Refutation not found, incomplete strategy% (5007)------------------------------
% 0.22/0.55  % (5007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5007)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5007)Memory used [KB]: 10746
% 0.22/0.55  % (5007)Time elapsed: 0.139 s
% 0.22/0.55  % (5007)------------------------------
% 0.22/0.55  % (5007)------------------------------
% 0.22/0.55  % (5001)Refutation not found, incomplete strategy% (5001)------------------------------
% 0.22/0.55  % (5001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (5001)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (5001)Memory used [KB]: 11001
% 0.22/0.55  % (5001)Time elapsed: 0.139 s
% 0.22/0.55  % (5001)------------------------------
% 0.22/0.55  % (5001)------------------------------
% 0.22/0.55  % (5011)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (5016)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (4995)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (5004)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.55  % (5003)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (5008)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (5020)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.56  % (5000)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (5006)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (5018)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (4998)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % (5014)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f423,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(subsumption_resolution,[],[f422,f416])).
% 0.22/0.56  fof(f416,plain,(
% 0.22/0.56    v2_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f408,f56])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f1])).
% 0.22/0.56  fof(f1,axiom,(
% 0.22/0.56    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 0.22/0.56  fof(f408,plain,(
% 0.22/0.56    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f257,f385])).
% 0.22/0.56  fof(f385,plain,(
% 0.22/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.56    inference(resolution,[],[f220,f202])).
% 0.22/0.56  fof(f202,plain,(
% 0.22/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.56    inference(forward_demodulation,[],[f200,f198])).
% 0.22/0.56  fof(f198,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f195,f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    v1_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f41,plain,(
% 0.22/0.56    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 0.22/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f19,f40,f39])).
% 0.22/0.56  fof(f39,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f40,plain,(
% 0.22/0.56    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 0.22/0.56    introduced(choice_axiom,[])).
% 0.22/0.56  fof(f19,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f16])).
% 0.22/0.56  fof(f16,negated_conjecture,(
% 0.22/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.56    inference(negated_conjecture,[],[f15])).
% 0.22/0.56  fof(f15,conjecture,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 0.22/0.56  fof(f195,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f149,f46])).
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f149,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f146,f47])).
% 0.22/0.56  fof(f47,plain,(
% 0.22/0.56    v1_funct_1(sK3)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (k1_partfun1(X3,X4,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.22/0.56    inference(resolution,[],[f78,f49])).
% 0.22/0.56  fof(f49,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f78,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.56  fof(f200,plain,(
% 0.22/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.22/0.56    inference(backward_demodulation,[],[f134,f198])).
% 0.22/0.56  fof(f134,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f133,f91])).
% 0.22/0.56  fof(f91,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f58,f57])).
% 0.22/0.56  fof(f57,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f17])).
% 0.22/0.56  fof(f17,plain,(
% 0.22/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.56  fof(f133,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    inference(resolution,[],[f76,f90])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.56    inference(forward_demodulation,[],[f51,f57])).
% 0.22/0.56  fof(f51,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.56  fof(f220,plain,(
% 0.22/0.56    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    inference(forward_demodulation,[],[f219,f198])).
% 0.22/0.56  fof(f219,plain,(
% 0.22/0.56    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f216,f44])).
% 0.22/0.56  fof(f216,plain,(
% 0.22/0.56    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f154,f46])).
% 0.22/0.56  fof(f154,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(X5)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f151,f47])).
% 0.22/0.56  fof(f151,plain,(
% 0.22/0.56    ( ! [X4,X5,X3] : (m1_subset_1(k1_partfun1(X3,X4,sK1,sK0,X5,sK3),k1_zfmisc_1(k2_zfmisc_1(X3,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X5)) )),
% 0.22/0.56    inference(resolution,[],[f80,f49])).
% 0.22/0.56  fof(f80,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 0.22/0.56    inference(forward_demodulation,[],[f256,f198])).
% 0.22/0.56  fof(f256,plain,(
% 0.22/0.56    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f255,f44])).
% 0.22/0.56  fof(f255,plain,(
% 0.22/0.56    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f254,f50])).
% 0.22/0.56  fof(f50,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f254,plain,(
% 0.22/0.56    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f253,f46])).
% 0.22/0.56  fof(f253,plain,(
% 0.22/0.56    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f173,f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f173,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~v1_funct_2(X3,X2,sK1) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | sK1 != k2_relset_1(X2,sK1,X3) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f172,f47])).
% 0.22/0.56  fof(f172,plain,(
% 0.22/0.56    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f171,f49])).
% 0.22/0.56  fof(f171,plain,(
% 0.22/0.56    ( ! [X2,X3] : (sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f170,f53])).
% 0.22/0.56  fof(f53,plain,(
% 0.22/0.56    k1_xboole_0 != sK0),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f170,plain,(
% 0.22/0.56    ( ! [X2,X3] : (k1_xboole_0 = sK0 | sK1 != k2_relset_1(X2,sK1,X3) | ~v2_funct_1(k1_partfun1(X2,sK1,sK1,sK0,X3,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) | ~v1_funct_2(X3,X2,sK1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(resolution,[],[f74,f48])).
% 0.22/0.56  fof(f48,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_2(X4,X1,X2) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v2_funct_1(X4) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 0.22/0.56  fof(f422,plain,(
% 0.22/0.56    ~v2_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f420,f273])).
% 0.22/0.56  fof(f273,plain,(
% 0.22/0.56    k6_relat_1(sK1) != k5_relat_1(sK3,sK2)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f268])).
% 0.22/0.56  fof(f268,plain,(
% 0.22/0.56    sK0 != sK0 | k6_relat_1(sK1) != k5_relat_1(sK3,sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f239,f263])).
% 0.22/0.56  fof(f263,plain,(
% 0.22/0.56    sK0 = k2_relat_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f103,f262])).
% 0.22/0.56  fof(f262,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f261,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.56    inference(backward_demodulation,[],[f90,f198])).
% 0.22/0.56  fof(f261,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    inference(forward_demodulation,[],[f260,f198])).
% 0.22/0.56  fof(f260,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f259,f47])).
% 0.22/0.56  fof(f259,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f258,f49])).
% 0.22/0.56  fof(f258,plain,(
% 0.22/0.56    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f158,f48])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_2(X0,sK1,sK0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f157,f44])).
% 0.22/0.56  fof(f157,plain,(
% 0.22/0.56    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f155,f46])).
% 0.22/0.56  fof(f155,plain,(
% 0.22/0.56    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f92,f45])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f71,f57])).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 0.22/0.56  fof(f103,plain,(
% 0.22/0.56    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f64,f49])).
% 0.22/0.56  fof(f64,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.22/0.56  fof(f239,plain,(
% 0.22/0.56    k6_relat_1(sK1) != k5_relat_1(sK3,sK2) | sK0 != k2_relat_1(sK3)),
% 0.22/0.56    inference(forward_demodulation,[],[f238,f105])).
% 0.22/0.56  fof(f105,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f102,f50])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f64,f46])).
% 0.22/0.56  fof(f238,plain,(
% 0.22/0.56    sK0 != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)),
% 0.22/0.56    inference(forward_demodulation,[],[f237,f123])).
% 0.22/0.56  fof(f123,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2)),
% 0.22/0.56    inference(backward_demodulation,[],[f99,f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f121,f46])).
% 0.22/0.56  fof(f121,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f119,f54])).
% 0.22/0.56  fof(f54,plain,(
% 0.22/0.56    k1_xboole_0 != sK1),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f119,plain,(
% 0.22/0.56    sK0 = k1_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    inference(resolution,[],[f65,f45])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f42])).
% 0.22/0.56  fof(f42,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.22/0.56  fof(f99,plain,(
% 0.22/0.56    k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f63,f46])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.22/0.56  fof(f237,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f236,f93])).
% 0.22/0.56  fof(f93,plain,(
% 0.22/0.56    v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f62,f46])).
% 0.22/0.56  fof(f62,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(ennf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.22/0.56  fof(f236,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relat_1(sK3) | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f235,f55])).
% 0.22/0.56  fof(f55,plain,(
% 0.22/0.56    k2_funct_1(sK2) != sK3),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f235,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3 | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(subsumption_resolution,[],[f232,f52])).
% 0.22/0.56  fof(f52,plain,(
% 0.22/0.56    v2_funct_1(sK2)),
% 0.22/0.56    inference(cnf_transformation,[],[f41])).
% 0.22/0.56  fof(f232,plain,(
% 0.22/0.56    k1_relat_1(sK2) != k2_relat_1(sK3) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = sK3 | k6_relat_1(k2_relat_1(sK2)) != k5_relat_1(sK3,sK2) | ~v1_relat_1(sK2)),
% 0.22/0.56    inference(resolution,[],[f144,f44])).
% 0.22/0.56  fof(f144,plain,(
% 0.22/0.56    ( ! [X1] : (~v1_funct_1(X1) | k2_relat_1(sK3) != k1_relat_1(X1) | ~v2_funct_1(X1) | sK3 = k2_funct_1(X1) | k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f141,f94])).
% 0.22/0.56  fof(f94,plain,(
% 0.22/0.56    v1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f62,f49])).
% 0.22/0.56  fof(f141,plain,(
% 0.22/0.56    ( ! [X1] : (k6_relat_1(k2_relat_1(X1)) != k5_relat_1(sK3,X1) | k2_relat_1(sK3) != k1_relat_1(X1) | ~v2_funct_1(X1) | sK3 = k2_funct_1(X1) | ~v1_relat_1(sK3) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.22/0.56    inference(resolution,[],[f61,f47])).
% 0.22/0.56  fof(f61,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v1_funct_1(X1) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | k2_funct_1(X0) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 0.22/0.56  fof(f420,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k5_relat_1(sK3,sK2) | ~v2_funct_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f128,f417])).
% 0.22/0.56  fof(f417,plain,(
% 0.22/0.56    sK2 = k2_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f415,f416])).
% 0.22/0.56  fof(f415,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f409])).
% 0.22/0.56  fof(f409,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f266,f385])).
% 0.22/0.56  fof(f266,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f231,f263])).
% 0.22/0.56  fof(f231,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f230,f94])).
% 0.22/0.56  fof(f230,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f224,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    sK1 = k1_relat_1(sK3)),
% 0.22/0.56    inference(backward_demodulation,[],[f100,f126])).
% 0.22/0.56  fof(f126,plain,(
% 0.22/0.56    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    inference(subsumption_resolution,[],[f125,f49])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    inference(subsumption_resolution,[],[f120,f53])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    inference(resolution,[],[f65,f48])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f63,f49])).
% 0.22/0.56  fof(f224,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f143,f47])).
% 0.22/0.56  fof(f143,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f142,f105])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f140,f93])).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(resolution,[],[f61,f44])).
% 0.22/0.56  fof(f128,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(sK1)),
% 0.22/0.56    inference(backward_demodulation,[],[f110,f127])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3))),
% 0.22/0.56    inference(subsumption_resolution,[],[f107,f94])).
% 0.22/0.56  fof(f107,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3)),
% 0.22/0.56    inference(resolution,[],[f59,f47])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f20])).
% 0.22/0.56  fof(f20,plain,(
% 0.22/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f2])).
% 0.22/0.56  fof(f2,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.57  % SZS output end Proof for theBenchmark
% 0.22/0.57  % (4998)------------------------------
% 0.22/0.57  % (4998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (4998)Termination reason: Refutation
% 0.22/0.57  
% 0.22/0.57  % (4998)Memory used [KB]: 2174
% 0.22/0.57  % (4998)Time elapsed: 0.081 s
% 0.22/0.57  % (4998)------------------------------
% 0.22/0.57  % (4998)------------------------------
% 0.22/0.57  % (5010)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (4990)Success in time 0.208 s
%------------------------------------------------------------------------------
