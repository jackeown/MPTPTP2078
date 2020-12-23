%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:30 EST 2020

% Result     : Theorem 1.95s
% Output     : Refutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :  213 (2984 expanded)
%              Number of leaves         :   22 ( 933 expanded)
%              Depth                    :   52
%              Number of atoms          :  881 (30320 expanded)
%              Number of equality atoms :  260 (10188 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f956,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f62,f932,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f932,plain,(
    ~ v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f931,f68])).

fof(f68,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50])).

fof(f50,plain,
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

fof(f51,plain,
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

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f931,plain,
    ( ~ v1_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f930,f242])).

fof(f242,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f240,f62])).

fof(f240,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f239,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f239,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f238,f60])).

fof(f60,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f238,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f237,f61])).

fof(f61,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f237,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f236,f62])).

fof(f236,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f235,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f235,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f234,f58])).

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f234,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f233,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f233,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f231,f199])).

fof(f199,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f64,f197])).

fof(f197,plain,(
    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f196,f57])).

fof(f196,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f195,f59])).

fof(f195,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f194,f60])).

fof(f194,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f192,f62])).

fof(f192,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f142,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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

fof(f142,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(subsumption_resolution,[],[f139,f105])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f70,f69])).

fof(f69,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f70,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f139,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f100,f64])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
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

fof(f64,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f231,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3) ),
    inference(superposition,[],[f95,f197])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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

fof(f930,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(subsumption_resolution,[],[f929,f60])).

fof(f929,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(trivial_inequality_removal,[],[f915])).

fof(f915,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k2_funct_1(sK2) = sK3 ),
    inference(superposition,[],[f415,f843])).

fof(f843,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f579,f836])).

fof(f836,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(resolution,[],[f820,f59])).

fof(f820,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sK2 = k2_funct_1(sK3) ) ),
    inference(resolution,[],[f804,f86])).

fof(f804,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f790])).

fof(f790,plain,
    ( sK1 != sK1
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f482,f777])).

fof(f777,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f776,f449])).

fof(f449,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f445,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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

fof(f445,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f444,f61])).

fof(f444,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f443,f239])).

fof(f443,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f337,f62])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK3) != X1
      | r1_tarski(k1_relat_1(sK3),X0)
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f336,f60])).

fof(f336,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(sK3),X0)
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f335,f263])).

fof(f263,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f262,f57])).

fof(f262,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f261,f58])).

fof(f261,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f260,f59])).

fof(f260,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f259,f60])).

fof(f259,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f258,f61])).

fof(f258,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f257,f62])).

fof(f257,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f256,f63])).

fof(f63,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f256,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f255,f66])).

fof(f66,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f52])).

fof(f255,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f253,f106])).

fof(f106,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f72,f69])).

fof(f72,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f253,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | k1_xboole_0 = sK0
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f98,f197])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | v2_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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

fof(f335,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(sK3),X0)
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ v2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f326,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f326,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | r1_tarski(k1_relat_1(sK3),X1) ) ),
    inference(superposition,[],[f121,f324])).

fof(f324,plain,(
    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f285,f62])).

fof(f285,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ) ),
    inference(resolution,[],[f264,f86])).

fof(f264,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f263,f130])).

fof(f130,plain,
    ( ~ v2_funct_1(sK3)
    | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f77,f60])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_relat_1(X0),X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(subsumption_resolution,[],[f120,f86])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r1_tarski(k2_relat_1(X0),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
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

fof(f776,plain,(
    r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f775,f61])).

fof(f775,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f774,f239])).

fof(f774,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | r1_tarski(sK1,k1_relat_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f633,f62])).

fof(f633,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK3) != X1
      | r1_tarski(sK1,k1_relat_1(sK3))
      | ~ v1_funct_2(sK3,X0,X1) ) ),
    inference(subsumption_resolution,[],[f632,f60])).

fof(f632,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,k1_relat_1(sK3))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(subsumption_resolution,[],[f631,f263])).

fof(f631,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK1,k1_relat_1(sK3))
      | k2_relset_1(X0,X1,sK3) != X1
      | ~ v2_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK3,X0,X1)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f622,f92])).

fof(f622,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k1_relat_1(sK3)) ) ),
    inference(resolution,[],[f617,f62])).

fof(f617,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK1,k1_relat_1(sK3))
      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f616,f86])).

fof(f616,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_funct_1(sK3))
      | r1_tarski(sK1,k1_relat_1(sK3))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f605,f86])).

fof(f605,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f604,f108])).

fof(f108,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f74,f69])).

fof(f74,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f604,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f585,f324])).

fof(f585,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k2_funct_1(sK3)))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(superposition,[],[f75,f579])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f482,plain,
    ( sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f481,f134])).

fof(f134,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f132,f59])).

fof(f132,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f87,f63])).

fof(f481,plain,
    ( ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f480,f57])).

fof(f480,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(trivial_inequality_removal,[],[f479])).

fof(f479,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | sK2 = k2_funct_1(sK3)
    | k2_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(superposition,[],[f478,f209])).

fof(f209,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f208,f57])).

fof(f208,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f207,f59])).

fof(f207,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f206,f60])).

fof(f206,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f202,f62])).

fof(f202,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f197,f102])).

fof(f102,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
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

fof(f478,plain,(
    ! [X0] :
      ( k6_partfun1(sK0) != k5_relat_1(X0,sK3)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_funct_1(sK3) = X0
      | k2_relat_1(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f453,f62])).

fof(f453,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(sK3) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k6_partfun1(sK0) != k5_relat_1(X0,sK3)
      | k2_relat_1(X0) != k1_relat_1(sK3) ) ),
    inference(resolution,[],[f271,f86])).

fof(f271,plain,(
    ! [X4] :
      ( ~ v1_relat_1(sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | k6_partfun1(sK0) != k5_relat_1(X4,sK3) ) ),
    inference(forward_demodulation,[],[f270,f242])).

fof(f270,plain,(
    ! [X4] :
      ( k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_relat_1(sK3) ) ),
    inference(subsumption_resolution,[],[f267,f60])).

fof(f267,plain,(
    ! [X4] :
      ( k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3)
      | k1_relat_1(sK3) != k2_relat_1(X4)
      | k2_funct_1(sK3) = X4
      | ~ v1_funct_1(X4)
      | ~ v1_relat_1(X4)
      | ~ v1_funct_1(sK3)
      | ~ v1_relat_1(sK3) ) ),
    inference(resolution,[],[f263,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f78,f69])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).

fof(f579,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f578,f61])).

fof(f578,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f577,f66])).

fof(f577,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(subsumption_resolution,[],[f576,f239])).

fof(f576,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ v1_funct_2(sK3,sK1,sK0) ),
    inference(resolution,[],[f269,f62])).

fof(f269,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | k1_xboole_0 = X2
      | ~ v1_funct_2(sK3,X3,X2) ) ),
    inference(subsumption_resolution,[],[f266,f60])).

fof(f266,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = X2
      | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3))
      | k2_relset_1(X3,X2,sK3) != X2
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
      | ~ v1_funct_2(sK3,X3,X2)
      | ~ v1_funct_1(sK3) ) ),
    inference(resolution,[],[f263,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f415,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0
      | k2_funct_1(sK2) = X0 ) ),
    inference(resolution,[],[f412,f59])).

fof(f412,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0
      | k5_relat_1(X0,sK2) != k6_partfun1(sK1) ) ),
    inference(resolution,[],[f402,f86])).

fof(f402,plain,(
    ! [X0] :
      ( ~ v1_relat_1(sK2)
      | k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) != sK0 ) ),
    inference(backward_demodulation,[],[f154,f396])).

fof(f396,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f393,f174])).

fof(f174,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK2))
    | sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f166,f85])).

fof(f166,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f165,f58])).

fof(f165,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(subsumption_resolution,[],[f164,f63])).

fof(f164,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(resolution,[],[f163,f59])).

fof(f163,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k2_relset_1(X3,X4,sK2) != X4
      | ~ v1_funct_2(sK2,X3,X4)
      | r1_tarski(k1_relat_1(sK2),X3) ) ),
    inference(subsumption_resolution,[],[f162,f57])).

fof(f162,plain,(
    ! [X4,X3] :
      ( k2_relset_1(X3,X4,sK2) != X4
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(sK2,X3,X4)
      | ~ v1_funct_1(sK2)
      | r1_tarski(k1_relat_1(sK2),X3) ) ),
    inference(subsumption_resolution,[],[f159,f65])).

fof(f65,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f159,plain,(
    ! [X4,X3] :
      ( k2_relset_1(X3,X4,sK2) != X4
      | ~ v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(sK2,X3,X4)
      | ~ v1_funct_1(sK2)
      | r1_tarski(k1_relat_1(sK2),X3) ) ),
    inference(resolution,[],[f92,f147])).

fof(f147,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | r1_tarski(k1_relat_1(sK2),X1) ) ),
    inference(superposition,[],[f121,f144])).

fof(f144,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f137,f59])).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ) ),
    inference(resolution,[],[f131,f86])).

fof(f131,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f129,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f57])).

fof(f393,plain,(
    r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f392,f58])).

fof(f392,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f391,f63])).

fof(f391,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | r1_tarski(sK0,k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f361,f59])).

fof(f361,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,sK2) != X1
      | r1_tarski(sK0,k1_relat_1(sK2))
      | ~ v1_funct_2(sK2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f360,f57])).

fof(f360,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,k1_relat_1(sK2))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(subsumption_resolution,[],[f359,f65])).

fof(f359,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK0,k1_relat_1(sK2))
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ v2_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f351,f92])).

fof(f351,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK0,k1_relat_1(sK2)) ) ),
    inference(resolution,[],[f338,f59])).

fof(f338,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | r1_tarski(sK0,k1_relat_1(sK2))
      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f287,f86])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(k2_funct_1(sK2))
      | r1_tarski(sK0,k1_relat_1(sK2))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(resolution,[],[f284,f86])).

fof(f284,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | r1_tarski(sK0,k1_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f283,f108])).

fof(f283,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f279,f144])).

fof(f279,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(superposition,[],[f75,f275])).

fof(f275,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f274,f58])).

fof(f274,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f273,f67])).

fof(f67,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f273,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f272,f63])).

fof(f272,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | k1_xboole_0 = sK1
    | ~ v1_funct_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f181,f59])).

fof(f181,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | k1_xboole_0 = X0
      | ~ v1_funct_2(sK2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f179,f57])).

fof(f179,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK2,X1,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f93,f65])).

fof(f154,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(sK1)
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(forward_demodulation,[],[f153,f134])).

fof(f153,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(sK2) ) ),
    inference(subsumption_resolution,[],[f151,f57])).

fof(f151,plain,(
    ! [X0] :
      ( k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2))
      | k2_relat_1(X0) != k1_relat_1(sK2)
      | k2_funct_1(sK2) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | ~ v1_funct_1(sK2)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f110,f65])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:31:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (24830)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.47  % (24814)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (24819)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.50  % (24810)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (24809)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (24811)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (24817)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.52  % (24827)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (24812)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (24808)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.54  % (24834)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24836)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (24823)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (24833)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (24826)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (24828)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (24837)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (24818)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.55  % (24829)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (24820)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (24815)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (24821)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (24831)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (24816)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (24825)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (24832)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (24813)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.57  % (24822)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (24835)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.57  % (24824)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (24824)Refutation not found, incomplete strategy% (24824)------------------------------
% 0.21/0.57  % (24824)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (24824)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (24824)Memory used [KB]: 10746
% 0.21/0.57  % (24824)Time elapsed: 0.166 s
% 0.21/0.57  % (24824)------------------------------
% 0.21/0.57  % (24824)------------------------------
% 1.95/0.62  % (24830)Refutation found. Thanks to Tanya!
% 1.95/0.62  % SZS status Theorem for theBenchmark
% 1.95/0.62  % SZS output start Proof for theBenchmark
% 1.95/0.62  fof(f956,plain,(
% 1.95/0.62    $false),
% 1.95/0.62    inference(unit_resulting_resolution,[],[f62,f932,f86])).
% 1.95/0.63  fof(f86,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f33])).
% 1.95/0.63  fof(f33,plain,(
% 1.95/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.63    inference(ennf_transformation,[],[f9])).
% 1.95/0.63  fof(f9,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.95/0.63  fof(f932,plain,(
% 1.95/0.63    ~v1_relat_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f931,f68])).
% 1.95/0.63  fof(f68,plain,(
% 1.95/0.63    k2_funct_1(sK2) != sK3),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f52,plain,(
% 1.95/0.63    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.95/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f51,f50])).
% 1.95/0.63  fof(f50,plain,(
% 1.95/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.95/0.63    introduced(choice_axiom,[])).
% 1.95/0.63  fof(f51,plain,(
% 1.95/0.63    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.95/0.63    introduced(choice_axiom,[])).
% 1.95/0.63  fof(f24,plain,(
% 1.95/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.95/0.63    inference(flattening,[],[f23])).
% 1.95/0.63  fof(f23,plain,(
% 1.95/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.95/0.63    inference(ennf_transformation,[],[f22])).
% 1.95/0.63  fof(f22,negated_conjecture,(
% 1.95/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.95/0.63    inference(negated_conjecture,[],[f21])).
% 1.95/0.63  fof(f21,conjecture,(
% 1.95/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.95/0.63  fof(f931,plain,(
% 1.95/0.63    ~v1_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 1.95/0.63    inference(subsumption_resolution,[],[f930,f242])).
% 1.95/0.63  fof(f242,plain,(
% 1.95/0.63    sK0 = k2_relat_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f240,f62])).
% 1.95/0.63  fof(f240,plain,(
% 1.95/0.63    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.95/0.63    inference(superposition,[],[f239,f87])).
% 1.95/0.63  fof(f87,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f34])).
% 1.95/0.63  fof(f34,plain,(
% 1.95/0.63    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.63    inference(ennf_transformation,[],[f11])).
% 1.95/0.63  fof(f11,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.95/0.63  fof(f239,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f238,f60])).
% 1.95/0.63  fof(f60,plain,(
% 1.95/0.63    v1_funct_1(sK3)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f238,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f237,f61])).
% 1.95/0.63  fof(f61,plain,(
% 1.95/0.63    v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f237,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f236,f62])).
% 1.95/0.63  fof(f236,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f235,f57])).
% 1.95/0.63  fof(f57,plain,(
% 1.95/0.63    v1_funct_1(sK2)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f235,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f234,f58])).
% 1.95/0.63  fof(f58,plain,(
% 1.95/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f234,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f233,f59])).
% 1.95/0.63  fof(f59,plain,(
% 1.95/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f233,plain,(
% 1.95/0.63    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f231,f199])).
% 1.95/0.63  fof(f199,plain,(
% 1.95/0.63    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 1.95/0.63    inference(backward_demodulation,[],[f64,f197])).
% 1.95/0.63  fof(f197,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f196,f57])).
% 1.95/0.63  fof(f196,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f195,f59])).
% 1.95/0.63  fof(f195,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f194,f60])).
% 1.95/0.63  fof(f194,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f192,f62])).
% 1.95/0.63  fof(f192,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(resolution,[],[f142,f104])).
% 1.95/0.63  fof(f104,plain,(
% 1.95/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f49])).
% 1.95/0.63  fof(f49,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.95/0.63    inference(flattening,[],[f48])).
% 1.95/0.63  fof(f48,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.95/0.63    inference(ennf_transformation,[],[f14])).
% 1.95/0.63  fof(f14,axiom,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.95/0.63  fof(f142,plain,(
% 1.95/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f139,f105])).
% 1.95/0.63  fof(f105,plain,(
% 1.95/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.95/0.63    inference(definition_unfolding,[],[f70,f69])).
% 1.95/0.63  fof(f69,plain,(
% 1.95/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f16])).
% 1.95/0.63  fof(f16,axiom,(
% 1.95/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.95/0.63  fof(f70,plain,(
% 1.95/0.63    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f13])).
% 1.95/0.63  fof(f13,axiom,(
% 1.95/0.63    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.95/0.63  fof(f139,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.95/0.63    inference(resolution,[],[f100,f64])).
% 1.95/0.63  fof(f100,plain,(
% 1.95/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f56])).
% 1.95/0.63  fof(f56,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.63    inference(nnf_transformation,[],[f45])).
% 1.95/0.63  fof(f45,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.63    inference(flattening,[],[f44])).
% 1.95/0.63  fof(f44,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.95/0.63    inference(ennf_transformation,[],[f12])).
% 1.95/0.63  fof(f12,axiom,(
% 1.95/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.95/0.63  fof(f64,plain,(
% 1.95/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f231,plain,(
% 1.95/0.63    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3)),
% 1.95/0.63    inference(superposition,[],[f95,f197])).
% 1.95/0.63  fof(f95,plain,(
% 1.95/0.63    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f41])).
% 1.95/0.63  fof(f41,plain,(
% 1.95/0.63    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.95/0.63    inference(flattening,[],[f40])).
% 1.95/0.63  fof(f40,plain,(
% 1.95/0.63    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.95/0.63    inference(ennf_transformation,[],[f17])).
% 1.95/0.63  fof(f17,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 1.95/0.63  fof(f930,plain,(
% 1.95/0.63    ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 1.95/0.63    inference(subsumption_resolution,[],[f929,f60])).
% 1.95/0.63  fof(f929,plain,(
% 1.95/0.63    ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 1.95/0.63    inference(trivial_inequality_removal,[],[f915])).
% 1.95/0.63  fof(f915,plain,(
% 1.95/0.63    k6_partfun1(sK1) != k6_partfun1(sK1) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | sK0 != k2_relat_1(sK3) | k2_funct_1(sK2) = sK3),
% 1.95/0.63    inference(superposition,[],[f415,f843])).
% 1.95/0.63  fof(f843,plain,(
% 1.95/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.95/0.63    inference(backward_demodulation,[],[f579,f836])).
% 1.95/0.63  fof(f836,plain,(
% 1.95/0.63    sK2 = k2_funct_1(sK3)),
% 1.95/0.63    inference(resolution,[],[f820,f59])).
% 1.95/0.63  fof(f820,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sK2 = k2_funct_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f804,f86])).
% 1.95/0.63  fof(f804,plain,(
% 1.95/0.63    ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 1.95/0.63    inference(trivial_inequality_removal,[],[f790])).
% 1.95/0.63  fof(f790,plain,(
% 1.95/0.63    sK1 != sK1 | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 1.95/0.63    inference(backward_demodulation,[],[f482,f777])).
% 1.95/0.63  fof(f777,plain,(
% 1.95/0.63    sK1 = k1_relat_1(sK3)),
% 1.95/0.63    inference(resolution,[],[f776,f449])).
% 1.95/0.63  fof(f449,plain,(
% 1.95/0.63    ~r1_tarski(sK1,k1_relat_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 1.95/0.63    inference(resolution,[],[f445,f85])).
% 1.95/0.63  fof(f85,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f55])).
% 1.95/0.63  fof(f55,plain,(
% 1.95/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/0.63    inference(flattening,[],[f54])).
% 1.95/0.63  fof(f54,plain,(
% 1.95/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.95/0.63    inference(nnf_transformation,[],[f1])).
% 1.95/0.63  fof(f1,axiom,(
% 1.95/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.95/0.63  fof(f445,plain,(
% 1.95/0.63    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.95/0.63    inference(subsumption_resolution,[],[f444,f61])).
% 1.95/0.63  fof(f444,plain,(
% 1.95/0.63    r1_tarski(k1_relat_1(sK3),sK1) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f443,f239])).
% 1.95/0.63  fof(f443,plain,(
% 1.95/0.63    sK0 != k2_relset_1(sK1,sK0,sK3) | r1_tarski(k1_relat_1(sK3),sK1) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(resolution,[],[f337,f62])).
% 1.95/0.63  fof(f337,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK3) != X1 | r1_tarski(k1_relat_1(sK3),X0) | ~v1_funct_2(sK3,X0,X1)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f336,f60])).
% 1.95/0.63  fof(f336,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(sK3),X0) | k2_relset_1(X0,X1,sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f335,f263])).
% 1.95/0.63  fof(f263,plain,(
% 1.95/0.63    v2_funct_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f262,f57])).
% 1.95/0.63  fof(f262,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f261,f58])).
% 1.95/0.63  fof(f261,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f260,f59])).
% 1.95/0.63  fof(f260,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f259,f60])).
% 1.95/0.63  fof(f259,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f258,f61])).
% 1.95/0.63  fof(f258,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f257,f62])).
% 1.95/0.63  fof(f257,plain,(
% 1.95/0.63    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f256,f63])).
% 1.95/0.63  fof(f63,plain,(
% 1.95/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f256,plain,(
% 1.95/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f255,f66])).
% 1.95/0.63  fof(f66,plain,(
% 1.95/0.63    k1_xboole_0 != sK0),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f255,plain,(
% 1.95/0.63    k1_xboole_0 = sK0 | sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f253,f106])).
% 1.95/0.63  fof(f106,plain,(
% 1.95/0.63    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.95/0.63    inference(definition_unfolding,[],[f72,f69])).
% 1.95/0.63  fof(f72,plain,(
% 1.95/0.63    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f5])).
% 1.95/0.63  fof(f5,axiom,(
% 1.95/0.63    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.95/0.63  fof(f253,plain,(
% 1.95/0.63    ~v2_funct_1(k6_partfun1(sK0)) | k1_xboole_0 = sK0 | sK1 != k2_relset_1(sK0,sK1,sK2) | v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(superposition,[],[f98,f197])).
% 1.95/0.63  fof(f98,plain,(
% 1.95/0.63    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | v2_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f43])).
% 1.95/0.63  fof(f43,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.95/0.63    inference(flattening,[],[f42])).
% 1.95/0.63  fof(f42,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.95/0.63    inference(ennf_transformation,[],[f18])).
% 1.95/0.63  fof(f18,axiom,(
% 1.95/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 1.95/0.63  fof(f335,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(k1_relat_1(sK3),X0) | k2_relset_1(X0,X1,sK3) != X1 | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f326,f92])).
% 1.95/0.63  fof(f92,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f37])).
% 1.95/0.63  fof(f37,plain,(
% 1.95/0.63    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.95/0.63    inference(flattening,[],[f36])).
% 1.95/0.63  fof(f36,plain,(
% 1.95/0.63    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.95/0.63    inference(ennf_transformation,[],[f19])).
% 1.95/0.63  fof(f19,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 1.95/0.63  fof(f326,plain,(
% 1.95/0.63    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k1_relat_1(sK3),X1)) )),
% 1.95/0.63    inference(superposition,[],[f121,f324])).
% 1.95/0.63  fof(f324,plain,(
% 1.95/0.63    k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.95/0.63    inference(resolution,[],[f285,f62])).
% 1.95/0.63  fof(f285,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))) )),
% 1.95/0.63    inference(resolution,[],[f264,f86])).
% 1.95/0.63  fof(f264,plain,(
% 1.95/0.63    ~v1_relat_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3))),
% 1.95/0.63    inference(resolution,[],[f263,f130])).
% 1.95/0.63  fof(f130,plain,(
% 1.95/0.63    ~v2_funct_1(sK3) | k1_relat_1(sK3) = k2_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.95/0.63    inference(resolution,[],[f77,f60])).
% 1.95/0.63  fof(f77,plain,(
% 1.95/0.63    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f27])).
% 1.95/0.63  fof(f27,plain,(
% 1.95/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.95/0.63    inference(flattening,[],[f26])).
% 1.95/0.63  fof(f26,plain,(
% 1.95/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.95/0.63    inference(ennf_transformation,[],[f7])).
% 1.95/0.63  fof(f7,axiom,(
% 1.95/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 1.95/0.63  fof(f121,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (r1_tarski(k2_relat_1(X0),X2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f120,f86])).
% 1.95/0.63  fof(f120,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r1_tarski(k2_relat_1(X0),X2) | ~v1_relat_1(X0)) )),
% 1.95/0.63    inference(resolution,[],[f89,f81])).
% 1.95/0.63  fof(f81,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f53])).
% 1.95/0.63  fof(f53,plain,(
% 1.95/0.63    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.95/0.63    inference(nnf_transformation,[],[f32])).
% 1.95/0.63  fof(f32,plain,(
% 1.95/0.63    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.95/0.63    inference(ennf_transformation,[],[f2])).
% 1.95/0.63  fof(f2,axiom,(
% 1.95/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.95/0.63  fof(f89,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(cnf_transformation,[],[f35])).
% 1.95/0.63  fof(f35,plain,(
% 1.95/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.95/0.63    inference(ennf_transformation,[],[f10])).
% 1.95/0.63  fof(f10,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.95/0.63  fof(f776,plain,(
% 1.95/0.63    r1_tarski(sK1,k1_relat_1(sK3))),
% 1.95/0.63    inference(subsumption_resolution,[],[f775,f61])).
% 1.95/0.63  fof(f775,plain,(
% 1.95/0.63    r1_tarski(sK1,k1_relat_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f774,f239])).
% 1.95/0.63  fof(f774,plain,(
% 1.95/0.63    sK0 != k2_relset_1(sK1,sK0,sK3) | r1_tarski(sK1,k1_relat_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(resolution,[],[f633,f62])).
% 1.95/0.63  fof(f633,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK3) != X1 | r1_tarski(sK1,k1_relat_1(sK3)) | ~v1_funct_2(sK3,X0,X1)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f632,f60])).
% 1.95/0.63  fof(f632,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(sK1,k1_relat_1(sK3)) | k2_relset_1(X0,X1,sK3) != X1 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f631,f263])).
% 1.95/0.63  fof(f631,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(sK1,k1_relat_1(sK3)) | k2_relset_1(X0,X1,sK3) != X1 | ~v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK3,X0,X1) | ~v1_funct_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f622,f92])).
% 1.95/0.63  fof(f622,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k1_relat_1(sK3))) )),
% 1.95/0.63    inference(resolution,[],[f617,f62])).
% 1.95/0.63  fof(f617,plain,(
% 1.95/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK1,k1_relat_1(sK3)) | ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.95/0.63    inference(resolution,[],[f616,f86])).
% 1.95/0.63  fof(f616,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(sK1,k1_relat_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(resolution,[],[f605,f86])).
% 1.95/0.63  fof(f605,plain,(
% 1.95/0.63    ~v1_relat_1(sK3) | ~v1_relat_1(k2_funct_1(sK3)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.95/0.63    inference(forward_demodulation,[],[f604,f108])).
% 1.95/0.63  fof(f108,plain,(
% 1.95/0.63    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.95/0.63    inference(definition_unfolding,[],[f74,f69])).
% 1.95/0.63  fof(f74,plain,(
% 1.95/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.95/0.63    inference(cnf_transformation,[],[f4])).
% 1.95/0.63  fof(f4,axiom,(
% 1.95/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.95/0.63  fof(f604,plain,(
% 1.95/0.63    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k1_relat_1(sK3)) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.95/0.63    inference(forward_demodulation,[],[f585,f324])).
% 1.95/0.63  fof(f585,plain,(
% 1.95/0.63    r1_tarski(k2_relat_1(k6_partfun1(sK1)),k2_relat_1(k2_funct_1(sK3))) | ~v1_relat_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.95/0.63    inference(superposition,[],[f75,f579])).
% 1.95/0.63  fof(f75,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f25])).
% 1.95/0.63  fof(f25,plain,(
% 1.95/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.95/0.63    inference(ennf_transformation,[],[f3])).
% 1.95/0.63  fof(f3,axiom,(
% 1.95/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.95/0.63  fof(f482,plain,(
% 1.95/0.63    sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3)),
% 1.95/0.63    inference(forward_demodulation,[],[f481,f134])).
% 1.95/0.63  fof(f134,plain,(
% 1.95/0.63    sK1 = k2_relat_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f132,f59])).
% 1.95/0.63  fof(f132,plain,(
% 1.95/0.63    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.95/0.63    inference(superposition,[],[f87,f63])).
% 1.95/0.63  fof(f481,plain,(
% 1.95/0.63    ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f480,f57])).
% 1.95/0.63  fof(f480,plain,(
% 1.95/0.63    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3)),
% 1.95/0.63    inference(trivial_inequality_removal,[],[f479])).
% 1.95/0.63  fof(f479,plain,(
% 1.95/0.63    k6_partfun1(sK0) != k6_partfun1(sK0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | sK2 = k2_funct_1(sK3) | k2_relat_1(sK2) != k1_relat_1(sK3)),
% 1.95/0.63    inference(superposition,[],[f478,f209])).
% 1.95/0.63  fof(f209,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.95/0.63    inference(subsumption_resolution,[],[f208,f57])).
% 1.95/0.63  fof(f208,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f207,f59])).
% 1.95/0.63  fof(f207,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f206,f60])).
% 1.95/0.63  fof(f206,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(subsumption_resolution,[],[f202,f62])).
% 1.95/0.63  fof(f202,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 1.95/0.63    inference(superposition,[],[f197,f102])).
% 1.95/0.63  fof(f102,plain,(
% 1.95/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f47])).
% 1.95/0.63  fof(f47,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.95/0.63    inference(flattening,[],[f46])).
% 1.95/0.63  fof(f46,plain,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.95/0.63    inference(ennf_transformation,[],[f15])).
% 1.95/0.63  fof(f15,axiom,(
% 1.95/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.95/0.63  fof(f478,plain,(
% 1.95/0.63    ( ! [X0] : (k6_partfun1(sK0) != k5_relat_1(X0,sK3) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_funct_1(sK3) = X0 | k2_relat_1(X0) != k1_relat_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f453,f62])).
% 1.95/0.63  fof(f453,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK3) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k6_partfun1(sK0) != k5_relat_1(X0,sK3) | k2_relat_1(X0) != k1_relat_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f271,f86])).
% 1.95/0.63  fof(f271,plain,(
% 1.95/0.63    ( ! [X4] : (~v1_relat_1(sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | k6_partfun1(sK0) != k5_relat_1(X4,sK3)) )),
% 1.95/0.63    inference(forward_demodulation,[],[f270,f242])).
% 1.95/0.63  fof(f270,plain,(
% 1.95/0.63    ( ! [X4] : (k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_relat_1(sK3)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f267,f60])).
% 1.95/0.63  fof(f267,plain,(
% 1.95/0.63    ( ! [X4] : (k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(X4,sK3) | k1_relat_1(sK3) != k2_relat_1(X4) | k2_funct_1(sK3) = X4 | ~v1_funct_1(X4) | ~v1_relat_1(X4) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f263,f110])).
% 1.95/0.63  fof(f110,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~v2_funct_1(X0) | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | k2_funct_1(X0) = X1 | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.95/0.63    inference(definition_unfolding,[],[f78,f69])).
% 1.95/0.63  fof(f78,plain,(
% 1.95/0.63    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f29])).
% 1.95/0.63  fof(f29,plain,(
% 1.95/0.63    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.95/0.63    inference(flattening,[],[f28])).
% 1.95/0.63  fof(f28,plain,(
% 1.95/0.63    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.95/0.63    inference(ennf_transformation,[],[f8])).
% 1.95/0.63  fof(f8,axiom,(
% 1.95/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_funct_1)).
% 1.95/0.63  fof(f579,plain,(
% 1.95/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 1.95/0.63    inference(subsumption_resolution,[],[f578,f61])).
% 1.95/0.63  fof(f578,plain,(
% 1.95/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f577,f66])).
% 1.95/0.63  fof(f577,plain,(
% 1.95/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f576,f239])).
% 1.95/0.63  fof(f576,plain,(
% 1.95/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | sK0 != k2_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~v1_funct_2(sK3,sK1,sK0)),
% 1.95/0.63    inference(resolution,[],[f269,f62])).
% 1.95/0.63  fof(f269,plain,(
% 1.95/0.63    ( ! [X2,X3] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | k1_xboole_0 = X2 | ~v1_funct_2(sK3,X3,X2)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f266,f60])).
% 1.95/0.63  fof(f266,plain,(
% 1.95/0.63    ( ! [X2,X3] : (k1_xboole_0 = X2 | k6_partfun1(X3) = k5_relat_1(sK3,k2_funct_1(sK3)) | k2_relset_1(X3,X2,sK3) != X2 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) | ~v1_funct_2(sK3,X3,X2) | ~v1_funct_1(sK3)) )),
% 1.95/0.63    inference(resolution,[],[f263,f93])).
% 1.95/0.63  fof(f93,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.95/0.63    inference(cnf_transformation,[],[f39])).
% 1.95/0.63  fof(f39,plain,(
% 1.95/0.63    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.95/0.63    inference(flattening,[],[f38])).
% 1.95/0.63  fof(f38,plain,(
% 1.95/0.63    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.95/0.63    inference(ennf_transformation,[],[f20])).
% 1.95/0.63  fof(f20,axiom,(
% 1.95/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.95/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.95/0.63  fof(f415,plain,(
% 1.95/0.63    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(sK1) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0 | k2_funct_1(sK2) = X0) )),
% 1.95/0.63    inference(resolution,[],[f412,f59])).
% 1.95/0.63  fof(f412,plain,(
% 1.95/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0 | k5_relat_1(X0,sK2) != k6_partfun1(sK1)) )),
% 1.95/0.63    inference(resolution,[],[f402,f86])).
% 1.95/0.63  fof(f402,plain,(
% 1.95/0.63    ( ! [X0] : (~v1_relat_1(sK2) | k5_relat_1(X0,sK2) != k6_partfun1(sK1) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) != sK0) )),
% 1.95/0.63    inference(backward_demodulation,[],[f154,f396])).
% 1.95/0.63  fof(f396,plain,(
% 1.95/0.63    sK0 = k1_relat_1(sK2)),
% 1.95/0.63    inference(resolution,[],[f393,f174])).
% 1.95/0.63  fof(f174,plain,(
% 1.95/0.63    ~r1_tarski(sK0,k1_relat_1(sK2)) | sK0 = k1_relat_1(sK2)),
% 1.95/0.63    inference(resolution,[],[f166,f85])).
% 1.95/0.63  fof(f166,plain,(
% 1.95/0.63    r1_tarski(k1_relat_1(sK2),sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f165,f58])).
% 1.95/0.63  fof(f165,plain,(
% 1.95/0.63    ~v1_funct_2(sK2,sK0,sK1) | r1_tarski(k1_relat_1(sK2),sK0)),
% 1.95/0.63    inference(subsumption_resolution,[],[f164,f63])).
% 1.95/0.63  fof(f164,plain,(
% 1.95/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v1_funct_2(sK2,sK0,sK1) | r1_tarski(k1_relat_1(sK2),sK0)),
% 1.95/0.63    inference(resolution,[],[f163,f59])).
% 1.95/0.63  fof(f163,plain,(
% 1.95/0.63    ( ! [X4,X3] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_relset_1(X3,X4,sK2) != X4 | ~v1_funct_2(sK2,X3,X4) | r1_tarski(k1_relat_1(sK2),X3)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f162,f57])).
% 1.95/0.63  fof(f162,plain,(
% 1.95/0.63    ( ! [X4,X3] : (k2_relset_1(X3,X4,sK2) != X4 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(sK2,X3,X4) | ~v1_funct_1(sK2) | r1_tarski(k1_relat_1(sK2),X3)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f159,f65])).
% 1.95/0.63  fof(f65,plain,(
% 1.95/0.63    v2_funct_1(sK2)),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f159,plain,(
% 1.95/0.63    ( ! [X4,X3] : (k2_relset_1(X3,X4,sK2) != X4 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(sK2,X3,X4) | ~v1_funct_1(sK2) | r1_tarski(k1_relat_1(sK2),X3)) )),
% 1.95/0.63    inference(resolution,[],[f92,f147])).
% 1.95/0.63  fof(f147,plain,(
% 1.95/0.63    ( ! [X2,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | r1_tarski(k1_relat_1(sK2),X1)) )),
% 1.95/0.63    inference(superposition,[],[f121,f144])).
% 1.95/0.63  fof(f144,plain,(
% 1.95/0.63    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.95/0.63    inference(resolution,[],[f137,f59])).
% 1.95/0.63  fof(f137,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))) )),
% 1.95/0.63    inference(resolution,[],[f131,f86])).
% 1.95/0.63  fof(f131,plain,(
% 1.95/0.63    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.95/0.63    inference(subsumption_resolution,[],[f129,f65])).
% 1.95/0.63  fof(f129,plain,(
% 1.95/0.63    ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.95/0.63    inference(resolution,[],[f77,f57])).
% 1.95/0.63  fof(f393,plain,(
% 1.95/0.63    r1_tarski(sK0,k1_relat_1(sK2))),
% 1.95/0.63    inference(subsumption_resolution,[],[f392,f58])).
% 1.95/0.63  fof(f392,plain,(
% 1.95/0.63    r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(subsumption_resolution,[],[f391,f63])).
% 1.95/0.63  fof(f391,plain,(
% 1.95/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(resolution,[],[f361,f59])).
% 1.95/0.63  fof(f361,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | r1_tarski(sK0,k1_relat_1(sK2)) | ~v1_funct_2(sK2,X0,X1)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f360,f57])).
% 1.95/0.63  fof(f360,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(sK0,k1_relat_1(sK2)) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f359,f65])).
% 1.95/0.63  fof(f359,plain,(
% 1.95/0.63    ( ! [X0,X1] : (r1_tarski(sK0,k1_relat_1(sK2)) | k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 1.95/0.63    inference(resolution,[],[f351,f92])).
% 1.95/0.63  fof(f351,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK0,k1_relat_1(sK2))) )),
% 1.95/0.63    inference(resolution,[],[f338,f59])).
% 1.95/0.63  fof(f338,plain,(
% 1.95/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | r1_tarski(sK0,k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.95/0.63    inference(resolution,[],[f287,f86])).
% 1.95/0.63  fof(f287,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(sK0,k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.95/0.63    inference(resolution,[],[f284,f86])).
% 1.95/0.63  fof(f284,plain,(
% 1.95/0.63    ~v1_relat_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | r1_tarski(sK0,k1_relat_1(sK2))),
% 1.95/0.63    inference(forward_demodulation,[],[f283,f108])).
% 1.95/0.63  fof(f283,plain,(
% 1.95/0.63    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.95/0.63    inference(forward_demodulation,[],[f279,f144])).
% 1.95/0.63  fof(f279,plain,(
% 1.95/0.63    r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 1.95/0.63    inference(superposition,[],[f75,f275])).
% 1.95/0.63  fof(f275,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.95/0.63    inference(subsumption_resolution,[],[f274,f58])).
% 1.95/0.63  fof(f274,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(subsumption_resolution,[],[f273,f67])).
% 1.95/0.63  fof(f67,plain,(
% 1.95/0.63    k1_xboole_0 != sK1),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  fof(f273,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(subsumption_resolution,[],[f272,f63])).
% 1.95/0.63  fof(f272,plain,(
% 1.95/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = sK1 | ~v1_funct_2(sK2,sK0,sK1)),
% 1.95/0.63    inference(resolution,[],[f181,f59])).
% 1.95/0.63  fof(f181,plain,(
% 1.95/0.63    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f179,f57])).
% 1.95/0.63  fof(f179,plain,(
% 1.95/0.63    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) )),
% 1.95/0.63    inference(resolution,[],[f93,f65])).
% 1.95/0.63  fof(f154,plain,(
% 1.95/0.63    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(sK1) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.95/0.63    inference(forward_demodulation,[],[f153,f134])).
% 1.95/0.63  fof(f153,plain,(
% 1.95/0.63    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_relat_1(sK2)) )),
% 1.95/0.63    inference(subsumption_resolution,[],[f151,f57])).
% 1.95/0.63  fof(f151,plain,(
% 1.95/0.63    ( ! [X0] : (k5_relat_1(X0,sK2) != k6_partfun1(k2_relat_1(sK2)) | k2_relat_1(X0) != k1_relat_1(sK2) | k2_funct_1(sK2) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) )),
% 1.95/0.63    inference(resolution,[],[f110,f65])).
% 1.95/0.63  fof(f62,plain,(
% 1.95/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.95/0.63    inference(cnf_transformation,[],[f52])).
% 1.95/0.63  % SZS output end Proof for theBenchmark
% 1.95/0.63  % (24830)------------------------------
% 1.95/0.63  % (24830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.63  % (24830)Termination reason: Refutation
% 1.95/0.63  
% 1.95/0.63  % (24830)Memory used [KB]: 7291
% 1.95/0.63  % (24830)Time elapsed: 0.199 s
% 1.95/0.63  % (24830)------------------------------
% 1.95/0.63  % (24830)------------------------------
% 1.95/0.64  % (24807)Success in time 0.277 s
%------------------------------------------------------------------------------
