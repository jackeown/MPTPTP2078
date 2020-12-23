%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:55 EST 2020

% Result     : Theorem 1.85s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  141 (1430 expanded)
%              Number of leaves         :   20 ( 447 expanded)
%              Depth                    :   23
%              Number of atoms          :  551 (14011 expanded)
%              Number of equality atoms :  182 (4828 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f510,plain,(
    $false ),
    inference(subsumption_resolution,[],[f509,f504])).

fof(f504,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f477,f63])).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f477,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f238,f468])).

fof(f468,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f386,f359])).

fof(f359,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f357,f355])).

fof(f355,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f271,f54])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).

fof(f44,plain,
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

fof(f45,plain,
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
    inference(flattening,[],[f21])).

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

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3) ) ),
    inference(resolution,[],[f213,f51])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f169,f49])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f169,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f85,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f357,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f160,f355])).

fof(f160,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f159,f96])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f64,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f159,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f83,f95])).

fof(f95,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(forward_demodulation,[],[f56,f61])).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

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

fof(f386,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(forward_demodulation,[],[f385,f355])).

fof(f385,plain,(
    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f275,f54])).

fof(f275,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f217,f51])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ) ),
    inference(resolution,[],[f171,f49])).

fof(f171,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ v1_funct_1(X9)
      | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6)))
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6))) ) ),
    inference(resolution,[],[f87,f52])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f238,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f237])).

fof(f237,plain,
    ( sK1 != sK1
    | ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f184,f236])).

fof(f236,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(forward_demodulation,[],[f225,f154])).

fof(f154,plain,(
    sK1 = k10_relat_1(sK3,sK0) ),
    inference(backward_demodulation,[],[f133,f153])).

fof(f153,plain,(
    sK1 = k1_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f152,f54])).

fof(f152,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f147,f58])).

fof(f58,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f46])).

fof(f147,plain,
    ( sK1 = k1_relset_1(sK1,sK0,sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(resolution,[],[f75,f53])).

fof(f53,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) = X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

% (5170)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f33,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f133,plain,(
    k1_relset_1(sK1,sK0,sK3) = k10_relat_1(sK3,sK0) ),
    inference(forward_demodulation,[],[f129,f120])).

fof(f120,plain,(
    ! [X1] : k8_relset_1(sK1,sK0,sK3,X1) = k10_relat_1(sK3,X1) ),
    inference(resolution,[],[f82,f54])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f129,plain,(
    k8_relset_1(sK1,sK0,sK3,sK0) = k1_relset_1(sK1,sK0,sK3) ),
    inference(resolution,[],[f74,f54])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f225,plain,(
    k10_relat_1(sK3,sK0) = k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f135,f223])).

fof(f223,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f115,f222])).

fof(f222,plain,(
    sK0 = k2_relset_1(sK1,sK0,sK3) ),
    inference(subsumption_resolution,[],[f221,f52])).

fof(f221,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f220,f54])).

fof(f220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f219,f95])).

fof(f219,plain,
    ( ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3) ),
    inference(resolution,[],[f175,f53])).

fof(f175,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK1,sK0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f174,f49])).

fof(f174,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(subsumption_resolution,[],[f172,f51])).

fof(f172,plain,(
    ! [X0] :
      ( sK0 = k2_relset_1(sK1,sK0,X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(X0,sK1,sK0)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f97,f50])).

fof(f50,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_2(X3,X1,X0)
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f81,f61])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f115,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f72,f54])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f135,plain,(
    k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(resolution,[],[f102,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f102,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f99,f71])).

fof(f71,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f99,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f66,f54])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f184,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f183,f102])).

fof(f183,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f144,f52])).

fof(f144,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(k5_relat_1(sK2,X0))
      | v2_funct_1(X0)
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f143,f117])).

fof(f117,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f114,f55])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f114,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f72,f51])).

fof(f143,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(k5_relat_1(sK2,X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f141,f101])).

fof(f101,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f98,f71])).

fof(f98,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f66,f51])).

fof(f141,plain,(
    ! [X0] :
      ( k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(k5_relat_1(sK2,X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f70,f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f509,plain,(
    ~ v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f507,f60])).

fof(f60,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f507,plain,
    ( k2_funct_1(sK2) = sK3
    | ~ v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f110,f505])).

fof(f505,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f503,f504])).

fof(f503,plain,
    ( ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(trivial_inequality_removal,[],[f478])).

fof(f478,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f240,f468])).

fof(f240,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | sK2 = k2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f231,f236])).

fof(f231,plain,
    ( k6_relat_1(sK0) != k5_relat_1(sK2,sK3)
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(backward_demodulation,[],[f198,f223])).

fof(f198,plain,
    ( k5_relat_1(sK2,sK3) != k6_relat_1(k2_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f193,f102])).

fof(f193,plain,
    ( k5_relat_1(sK2,sK3) != k6_relat_1(k2_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK2 = k2_funct_1(sK3)
    | sK1 != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f166,f52])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | k1_relat_1(X0) != sK1
      | ~ v1_relat_1(X0) ) ),
    inference(forward_demodulation,[],[f165,f117])).

fof(f165,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f163,f101])).

fof(f163,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0)
      | k1_relat_1(X0) != k2_relat_1(sK2)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = sK2
      | ~ v1_relat_1(sK2)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f68,f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f110,plain,
    ( ~ v2_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f107,f102])).

fof(f107,plain,
    ( ~ v2_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f67,f52])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:21:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (5185)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (5181)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.56  % (5173)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.56  % (5169)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.57  % (5159)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.57  % (5158)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.57  % (5177)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (5165)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.58  % (5164)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.55/0.59  % (5163)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.55/0.59  % (5162)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.55/0.59  % (5161)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.59  % (5184)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.60  % (5176)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.60  % (5160)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.55/0.60  % (5187)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.85/0.60  % (5183)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.85/0.60  % (5180)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.85/0.60  % (5174)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.85/0.60  % (5179)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.85/0.60  % (5174)Refutation not found, incomplete strategy% (5174)------------------------------
% 1.85/0.60  % (5174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.60  % (5174)Termination reason: Refutation not found, incomplete strategy
% 1.85/0.60  
% 1.85/0.60  % (5174)Memory used [KB]: 10746
% 1.85/0.60  % (5174)Time elapsed: 0.173 s
% 1.85/0.60  % (5174)------------------------------
% 1.85/0.60  % (5174)------------------------------
% 1.85/0.60  % (5178)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.85/0.60  % (5167)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.85/0.61  % (5168)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.85/0.61  % (5166)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.85/0.61  % (5186)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.85/0.61  % (5171)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.85/0.61  % (5182)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.85/0.61  % (5172)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.85/0.61  % (5175)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.85/0.62  % (5165)Refutation found. Thanks to Tanya!
% 1.85/0.62  % SZS status Theorem for theBenchmark
% 1.85/0.62  % SZS output start Proof for theBenchmark
% 1.85/0.62  fof(f510,plain,(
% 1.85/0.62    $false),
% 1.85/0.62    inference(subsumption_resolution,[],[f509,f504])).
% 1.85/0.62  fof(f504,plain,(
% 1.85/0.62    v2_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f477,f63])).
% 1.85/0.62  fof(f63,plain,(
% 1.85/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f4])).
% 1.85/0.62  fof(f4,axiom,(
% 1.85/0.62    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.85/0.62  fof(f477,plain,(
% 1.85/0.62    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f238,f468])).
% 1.85/0.62  fof(f468,plain,(
% 1.85/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.85/0.62    inference(resolution,[],[f386,f359])).
% 1.85/0.62  fof(f359,plain,(
% 1.85/0.62    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.85/0.62    inference(forward_demodulation,[],[f357,f355])).
% 1.85/0.62  fof(f355,plain,(
% 1.85/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.85/0.62    inference(resolution,[],[f271,f54])).
% 1.85/0.62  fof(f54,plain,(
% 1.85/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f46,plain,(
% 1.85/0.62    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.85/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f45,f44])).
% 1.85/0.62  fof(f44,plain,(
% 1.85/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.85/0.62    introduced(choice_axiom,[])).
% 1.85/0.62  fof(f45,plain,(
% 1.85/0.62    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.85/0.62    introduced(choice_axiom,[])).
% 1.85/0.62  fof(f22,plain,(
% 1.85/0.62    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.85/0.62    inference(flattening,[],[f21])).
% 1.85/0.62  fof(f21,plain,(
% 1.85/0.62    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.85/0.62    inference(ennf_transformation,[],[f19])).
% 1.85/0.62  fof(f19,negated_conjecture,(
% 1.85/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.85/0.62    inference(negated_conjecture,[],[f18])).
% 1.85/0.62  fof(f18,conjecture,(
% 1.85/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 1.85/0.62  fof(f271,plain,(
% 1.85/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(sK0,sK1,X0,X1,sK2,sK3)) )),
% 1.85/0.62    inference(resolution,[],[f213,f51])).
% 1.85/0.62  fof(f51,plain,(
% 1.85/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f213,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relat_1(sK2,sK3) = k1_partfun1(X0,X1,X2,X3,sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.85/0.62    inference(resolution,[],[f169,f49])).
% 1.85/0.62  fof(f49,plain,(
% 1.85/0.62    v1_funct_1(sK2)),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f169,plain,(
% 1.85/0.62    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | k1_partfun1(X7,X8,X5,X6,X9,sK3) = k5_relat_1(X9,sK3) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.85/0.62    inference(resolution,[],[f85,f52])).
% 1.85/0.62  fof(f52,plain,(
% 1.85/0.62    v1_funct_1(sK3)),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f85,plain,(
% 1.85/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f41])).
% 1.85/0.62  fof(f41,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.85/0.62    inference(flattening,[],[f40])).
% 1.85/0.62  fof(f40,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.85/0.62    inference(ennf_transformation,[],[f15])).
% 1.85/0.62  fof(f15,axiom,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.85/0.62  fof(f357,plain,(
% 1.85/0.62    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.85/0.62    inference(backward_demodulation,[],[f160,f355])).
% 1.85/0.62  fof(f160,plain,(
% 1.85/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.85/0.62    inference(subsumption_resolution,[],[f159,f96])).
% 1.85/0.62  fof(f96,plain,(
% 1.85/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.85/0.62    inference(forward_demodulation,[],[f64,f61])).
% 1.85/0.62  fof(f61,plain,(
% 1.85/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f16])).
% 1.85/0.62  fof(f16,axiom,(
% 1.85/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.85/0.62  fof(f64,plain,(
% 1.85/0.62    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f20])).
% 1.85/0.62  fof(f20,plain,(
% 1.85/0.62    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.85/0.62    inference(pure_predicate_removal,[],[f14])).
% 1.85/0.62  fof(f14,axiom,(
% 1.85/0.62    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.85/0.62  fof(f159,plain,(
% 1.85/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.85/0.62    inference(resolution,[],[f83,f95])).
% 1.85/0.62  fof(f95,plain,(
% 1.85/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.85/0.62    inference(forward_demodulation,[],[f56,f61])).
% 1.85/0.62  fof(f56,plain,(
% 1.85/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f83,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f48])).
% 1.85/0.62  fof(f48,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(nnf_transformation,[],[f39])).
% 1.85/0.62  fof(f39,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(flattening,[],[f38])).
% 1.85/0.62  fof(f38,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.85/0.62    inference(ennf_transformation,[],[f10])).
% 1.85/0.62  fof(f10,axiom,(
% 1.85/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.85/0.62  fof(f386,plain,(
% 1.85/0.62    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.85/0.62    inference(forward_demodulation,[],[f385,f355])).
% 1.85/0.62  fof(f385,plain,(
% 1.85/0.62    m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.85/0.62    inference(resolution,[],[f275,f54])).
% 1.85/0.62  fof(f275,plain,(
% 1.85/0.62    ( ! [X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(sK0,sK1,X0,X1,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 1.85/0.62    inference(resolution,[],[f217,f51])).
% 1.85/0.62  fof(f217,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))) )),
% 1.85/0.62    inference(resolution,[],[f171,f49])).
% 1.85/0.62  fof(f171,plain,(
% 1.85/0.62    ( ! [X6,X8,X7,X5,X9] : (~v1_funct_1(X9) | m1_subset_1(k1_partfun1(X7,X8,X5,X6,X9,sK3),k1_zfmisc_1(k2_zfmisc_1(X7,X6))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X7,X8))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))) )),
% 1.85/0.62    inference(resolution,[],[f87,f52])).
% 1.85/0.62  fof(f87,plain,(
% 1.85/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f43])).
% 1.85/0.62  fof(f43,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.85/0.62    inference(flattening,[],[f42])).
% 1.85/0.62  fof(f42,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.85/0.62    inference(ennf_transformation,[],[f13])).
% 1.85/0.62  fof(f13,axiom,(
% 1.85/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.85/0.62  fof(f238,plain,(
% 1.85/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 1.85/0.62    inference(trivial_inequality_removal,[],[f237])).
% 1.85/0.62  fof(f237,plain,(
% 1.85/0.62    sK1 != sK1 | ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f184,f236])).
% 1.85/0.62  fof(f236,plain,(
% 1.85/0.62    sK1 = k1_relat_1(sK3)),
% 1.85/0.62    inference(forward_demodulation,[],[f225,f154])).
% 1.85/0.62  fof(f154,plain,(
% 1.85/0.62    sK1 = k10_relat_1(sK3,sK0)),
% 1.85/0.62    inference(backward_demodulation,[],[f133,f153])).
% 1.85/0.62  fof(f153,plain,(
% 1.85/0.62    sK1 = k1_relset_1(sK1,sK0,sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f152,f54])).
% 1.85/0.62  fof(f152,plain,(
% 1.85/0.62    sK1 = k1_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.85/0.62    inference(subsumption_resolution,[],[f147,f58])).
% 1.85/0.62  fof(f58,plain,(
% 1.85/0.62    k1_xboole_0 != sK0),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f147,plain,(
% 1.85/0.62    sK1 = k1_relset_1(sK1,sK0,sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.85/0.62    inference(resolution,[],[f75,f53])).
% 1.85/0.62  fof(f53,plain,(
% 1.85/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f75,plain,(
% 1.85/0.62    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f47])).
% 1.85/0.62  fof(f47,plain,(
% 1.85/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(nnf_transformation,[],[f34])).
% 1.85/0.62  fof(f34,plain,(
% 1.85/0.62    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(flattening,[],[f33])).
% 1.85/0.62  % (5170)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.85/0.62  fof(f33,plain,(
% 1.85/0.62    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(ennf_transformation,[],[f12])).
% 1.85/0.62  fof(f12,axiom,(
% 1.85/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.85/0.62  fof(f133,plain,(
% 1.85/0.62    k1_relset_1(sK1,sK0,sK3) = k10_relat_1(sK3,sK0)),
% 1.85/0.62    inference(forward_demodulation,[],[f129,f120])).
% 1.85/0.62  fof(f120,plain,(
% 1.85/0.62    ( ! [X1] : (k8_relset_1(sK1,sK0,sK3,X1) = k10_relat_1(sK3,X1)) )),
% 1.85/0.62    inference(resolution,[],[f82,f54])).
% 1.85/0.62  fof(f82,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f37])).
% 1.85/0.62  fof(f37,plain,(
% 1.85/0.62    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(ennf_transformation,[],[f9])).
% 1.85/0.62  fof(f9,axiom,(
% 1.85/0.62    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.85/0.62  fof(f129,plain,(
% 1.85/0.62    k8_relset_1(sK1,sK0,sK3,sK0) = k1_relset_1(sK1,sK0,sK3)),
% 1.85/0.62    inference(resolution,[],[f74,f54])).
% 1.85/0.62  fof(f74,plain,(
% 1.85/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f32])).
% 1.85/0.62  fof(f32,plain,(
% 1.85/0.62    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(ennf_transformation,[],[f11])).
% 1.85/0.62  fof(f11,axiom,(
% 1.85/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.85/0.62  fof(f225,plain,(
% 1.85/0.62    k10_relat_1(sK3,sK0) = k1_relat_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f135,f223])).
% 1.85/0.62  fof(f223,plain,(
% 1.85/0.62    sK0 = k2_relat_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f115,f222])).
% 1.85/0.62  fof(f222,plain,(
% 1.85/0.62    sK0 = k2_relset_1(sK1,sK0,sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f221,f52])).
% 1.85/0.62  fof(f221,plain,(
% 1.85/0.62    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f220,f54])).
% 1.85/0.62  fof(f220,plain,(
% 1.85/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f219,f95])).
% 1.85/0.62  fof(f219,plain,(
% 1.85/0.62    ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f175,f53])).
% 1.85/0.62  fof(f175,plain,(
% 1.85/0.62    ( ! [X0] : (~v1_funct_2(X0,sK1,sK0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 = k2_relset_1(sK1,sK0,X0) | ~v1_funct_1(X0)) )),
% 1.85/0.62    inference(subsumption_resolution,[],[f174,f49])).
% 1.85/0.62  fof(f174,plain,(
% 1.85/0.62    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.85/0.62    inference(subsumption_resolution,[],[f172,f51])).
% 1.85/0.62  fof(f172,plain,(
% 1.85/0.62    ( ! [X0] : (sK0 = k2_relset_1(sK1,sK0,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X0),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(X0,sK1,sK0) | ~v1_funct_1(X0)) )),
% 1.85/0.62    inference(resolution,[],[f97,f50])).
% 1.85/0.62  fof(f50,plain,(
% 1.85/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f97,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (~v1_funct_2(X3,X1,X0) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.85/0.62    inference(forward_demodulation,[],[f81,f61])).
% 1.85/0.62  fof(f81,plain,(
% 1.85/0.62    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f36])).
% 1.85/0.62  fof(f36,plain,(
% 1.85/0.62    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.85/0.62    inference(flattening,[],[f35])).
% 1.85/0.62  fof(f35,plain,(
% 1.85/0.62    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.85/0.62    inference(ennf_transformation,[],[f17])).
% 1.85/0.62  fof(f17,axiom,(
% 1.85/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 1.85/0.62  fof(f115,plain,(
% 1.85/0.62    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f72,f54])).
% 1.85/0.62  fof(f72,plain,(
% 1.85/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f31])).
% 1.85/0.62  fof(f31,plain,(
% 1.85/0.62    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.85/0.62    inference(ennf_transformation,[],[f8])).
% 1.85/0.62  fof(f8,axiom,(
% 1.85/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.85/0.62  fof(f135,plain,(
% 1.85/0.62    k10_relat_1(sK3,k2_relat_1(sK3)) = k1_relat_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f102,f65])).
% 1.85/0.62  fof(f65,plain,(
% 1.85/0.62    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f23])).
% 1.85/0.62  fof(f23,plain,(
% 1.85/0.62    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.62    inference(ennf_transformation,[],[f3])).
% 1.85/0.62  fof(f3,axiom,(
% 1.85/0.62    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.85/0.62  fof(f102,plain,(
% 1.85/0.62    v1_relat_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f99,f71])).
% 1.85/0.62  fof(f71,plain,(
% 1.85/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.85/0.62    inference(cnf_transformation,[],[f2])).
% 1.85/0.62  fof(f2,axiom,(
% 1.85/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.85/0.62  fof(f99,plain,(
% 1.85/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 1.85/0.62    inference(resolution,[],[f66,f54])).
% 1.85/0.62  fof(f66,plain,(
% 1.85/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f24])).
% 1.85/0.62  fof(f24,plain,(
% 1.85/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.85/0.62    inference(ennf_transformation,[],[f1])).
% 1.85/0.62  fof(f1,axiom,(
% 1.85/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.85/0.62  fof(f184,plain,(
% 1.85/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f183,f102])).
% 1.85/0.62  fof(f183,plain,(
% 1.85/0.62    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f144,f52])).
% 1.85/0.62  fof(f144,plain,(
% 1.85/0.62    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(k5_relat_1(sK2,X0)) | v2_funct_1(X0) | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(forward_demodulation,[],[f143,f117])).
% 1.85/0.62  fof(f117,plain,(
% 1.85/0.62    sK1 = k2_relat_1(sK2)),
% 1.85/0.62    inference(forward_demodulation,[],[f114,f55])).
% 1.85/0.62  fof(f55,plain,(
% 1.85/0.62    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f114,plain,(
% 1.85/0.62    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 1.85/0.62    inference(resolution,[],[f72,f51])).
% 1.85/0.62  fof(f143,plain,(
% 1.85/0.62    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X0)) | v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(subsumption_resolution,[],[f141,f101])).
% 1.85/0.62  fof(f101,plain,(
% 1.85/0.62    v1_relat_1(sK2)),
% 1.85/0.62    inference(subsumption_resolution,[],[f98,f71])).
% 1.85/0.62  fof(f98,plain,(
% 1.85/0.62    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.85/0.62    inference(resolution,[],[f66,f51])).
% 1.85/0.62  fof(f141,plain,(
% 1.85/0.62    ( ! [X0] : (k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(k5_relat_1(sK2,X0)) | v2_funct_1(X0) | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(resolution,[],[f70,f49])).
% 1.85/0.62  fof(f70,plain,(
% 1.85/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f30])).
% 1.85/0.62  fof(f30,plain,(
% 1.85/0.62    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.62    inference(flattening,[],[f29])).
% 1.85/0.62  fof(f29,plain,(
% 1.85/0.62    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.85/0.62    inference(ennf_transformation,[],[f5])).
% 1.85/0.62  fof(f5,axiom,(
% 1.85/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.85/0.62  fof(f509,plain,(
% 1.85/0.62    ~v2_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f507,f60])).
% 1.85/0.62  fof(f60,plain,(
% 1.85/0.62    k2_funct_1(sK2) != sK3),
% 1.85/0.62    inference(cnf_transformation,[],[f46])).
% 1.85/0.62  fof(f507,plain,(
% 1.85/0.62    k2_funct_1(sK2) = sK3 | ~v2_funct_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f110,f505])).
% 1.85/0.62  fof(f505,plain,(
% 1.85/0.62    sK2 = k2_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f503,f504])).
% 1.85/0.62  fof(f503,plain,(
% 1.85/0.62    ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 1.85/0.62    inference(trivial_inequality_removal,[],[f478])).
% 1.85/0.62  fof(f478,plain,(
% 1.85/0.62    k6_relat_1(sK0) != k6_relat_1(sK0) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f240,f468])).
% 1.85/0.62  fof(f240,plain,(
% 1.85/0.62    ~v2_funct_1(sK3) | k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | sK2 = k2_funct_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f231,f236])).
% 1.85/0.62  fof(f231,plain,(
% 1.85/0.62    k6_relat_1(sK0) != k5_relat_1(sK2,sK3) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.85/0.62    inference(backward_demodulation,[],[f198,f223])).
% 1.85/0.62  fof(f198,plain,(
% 1.85/0.62    k5_relat_1(sK2,sK3) != k6_relat_1(k2_relat_1(sK3)) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3)),
% 1.85/0.62    inference(subsumption_resolution,[],[f193,f102])).
% 1.85/0.62  fof(f193,plain,(
% 1.85/0.62    k5_relat_1(sK2,sK3) != k6_relat_1(k2_relat_1(sK3)) | ~v2_funct_1(sK3) | sK2 = k2_funct_1(sK3) | sK1 != k1_relat_1(sK3) | ~v1_relat_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f166,f52])).
% 1.85/0.62  fof(f166,plain,(
% 1.85/0.62    ( ! [X0] : (~v1_funct_1(X0) | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | k1_relat_1(X0) != sK1 | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(forward_demodulation,[],[f165,f117])).
% 1.85/0.62  fof(f165,plain,(
% 1.85/0.62    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(subsumption_resolution,[],[f163,f101])).
% 1.85/0.62  fof(f163,plain,(
% 1.85/0.62    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(sK2,X0) | k1_relat_1(X0) != k2_relat_1(sK2) | ~v2_funct_1(X0) | k2_funct_1(X0) = sK2 | ~v1_relat_1(sK2) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(resolution,[],[f68,f49])).
% 1.85/0.62  fof(f68,plain,(
% 1.85/0.62    ( ! [X0,X1] : (~v1_funct_1(X1) | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | k2_funct_1(X0) = X1 | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f28])).
% 1.85/0.62  fof(f28,plain,(
% 1.85/0.62    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.62    inference(flattening,[],[f27])).
% 1.85/0.62  fof(f27,plain,(
% 1.85/0.62    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.85/0.62    inference(ennf_transformation,[],[f6])).
% 1.85/0.62  fof(f6,axiom,(
% 1.85/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.85/0.62  fof(f110,plain,(
% 1.85/0.62    ~v2_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 1.85/0.62    inference(subsumption_resolution,[],[f107,f102])).
% 1.85/0.62  fof(f107,plain,(
% 1.85/0.62    ~v2_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3)) | ~v1_relat_1(sK3)),
% 1.85/0.62    inference(resolution,[],[f67,f52])).
% 1.85/0.62  fof(f67,plain,(
% 1.85/0.62    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 1.85/0.62    inference(cnf_transformation,[],[f26])).
% 1.85/0.62  fof(f26,plain,(
% 1.85/0.62    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.85/0.62    inference(flattening,[],[f25])).
% 1.85/0.62  fof(f25,plain,(
% 1.85/0.62    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.85/0.62    inference(ennf_transformation,[],[f7])).
% 1.85/0.62  fof(f7,axiom,(
% 1.85/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.85/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.85/0.62  % SZS output end Proof for theBenchmark
% 1.85/0.62  % (5165)------------------------------
% 1.85/0.62  % (5165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.85/0.62  % (5165)Termination reason: Refutation
% 1.85/0.62  
% 1.85/0.62  % (5165)Memory used [KB]: 2174
% 1.85/0.62  % (5165)Time elapsed: 0.141 s
% 1.85/0.62  % (5165)------------------------------
% 1.85/0.62  % (5165)------------------------------
% 1.85/0.63  % (5157)Success in time 0.265 s
%------------------------------------------------------------------------------
