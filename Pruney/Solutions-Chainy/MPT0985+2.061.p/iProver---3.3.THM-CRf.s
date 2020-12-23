%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:32 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  175 (10750 expanded)
%              Number of clauses        :  113 (3644 expanded)
%              Number of leaves         :   14 (2016 expanded)
%              Depth                    :   28
%              Number of atoms          :  507 (55423 expanded)
%              Number of equality atoms :  265 (11604 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f52])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f55,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f56,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f62,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f56,f62])).

fof(f103,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f63])).

fof(f104,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f63])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f82,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f102,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f101,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f63])).

fof(f81,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f107,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f63])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f57])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f109,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f108,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f69])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f113,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f91])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_801,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_42])).

cnf(c_802,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_801])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_804,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_802,c_41])).

cnf(c_1558,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1564,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4048,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1558,c_1564])).

cnf(c_4333,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_804,c_4048])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1566,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2809,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1566])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_529,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_40])).

cnf(c_530,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_532,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_43])).

cnf(c_1552,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_2829,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2809,c_1552])).

cnf(c_35,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1559,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3928,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2829,c_1559])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1563,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3189,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1558,c_1563])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_3204,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_3189,c_39])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_515,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_40])).

cnf(c_516,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_518,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_43])).

cnf(c_1553,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_2828,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2809,c_1553])).

cnf(c_3216,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3204,c_2828])).

cnf(c_3954,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3928,c_3216])).

cnf(c_44,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_46,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1884,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1885,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1884])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1892,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1893,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1892])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1912,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_5030,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3954,c_44,c_46,c_1885,c_1893,c_1912])).

cnf(c_5037,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5030,c_1564])).

cnf(c_5054,plain,
    ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5037,c_3216])).

cnf(c_5138,plain,
    ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4333,c_5054])).

cnf(c_36,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_38,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_825,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_36,c_38])).

cnf(c_826,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_825])).

cnf(c_838,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_826,c_19])).

cnf(c_1540,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_838])).

cnf(c_827,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_826])).

cnf(c_2148,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1540,c_44,c_46,c_827,c_1885,c_1893,c_1912])).

cnf(c_2149,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2148])).

cnf(c_2950,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k2_relat_1(sK3) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2828,c_2149])).

cnf(c_3014,plain,
    ( k2_relat_1(sK3) != sK2
    | k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2950,c_2829])).

cnf(c_3213,plain,
    ( k1_relat_1(sK3) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3204,c_3014])).

cnf(c_3228,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3213])).

cnf(c_4606,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_3228])).

cnf(c_5035,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4333,c_5030])).

cnf(c_5139,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5138,c_4606,c_5035])).

cnf(c_5143,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5139,c_5030])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_5248,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5143,c_4])).

cnf(c_4051,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1564])).

cnf(c_5545,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_5248,c_4051])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1572,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4796,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1572])).

cnf(c_5146,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5139,c_4796])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_5241,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5146,c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_147,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5737,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5241,c_147])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1573,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5742,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5737,c_1573])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1565,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5039,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5030,c_1565])).

cnf(c_5542,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5248,c_1572])).

cnf(c_8381,plain,
    ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5039,c_147,c_5542])).

cnf(c_8385,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8381,c_5742])).

cnf(c_8388,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8385,c_1573])).

cnf(c_5157,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5139,c_3216])).

cnf(c_6329,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5742,c_5157])).

cnf(c_8517,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8388,c_6329])).

cnf(c_9230,plain,
    ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5545,c_5742,c_8388,c_8517])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_718,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_38])).

cnf(c_719,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_718])).

cnf(c_1545,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_1783,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1545,c_4])).

cnf(c_2237,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | sK2 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1783,c_44,c_46,c_1885,c_1912])).

cnf(c_2238,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2237])).

cnf(c_5160,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5139,c_2238])).

cnf(c_5199,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5160])).

cnf(c_5203,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5199,c_4])).

cnf(c_5251,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5248,c_5203])).

cnf(c_9197,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5251,c_5742,c_8388])).

cnf(c_9232,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9230,c_9197])).

cnf(c_140,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_139,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9232,c_140,c_139])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:05:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.99  
% 3.23/0.99  ------  iProver source info
% 3.23/0.99  
% 3.23/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.99  git: non_committed_changes: false
% 3.23/0.99  git: last_make_outside_of_git: false
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     num_symb
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       true
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  ------ Parsing...
% 3.23/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.99  ------ Proving...
% 3.23/0.99  ------ Problem Properties 
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  clauses                                 45
% 3.23/0.99  conjectures                             3
% 3.23/0.99  EPR                                     3
% 3.23/0.99  Horn                                    38
% 3.23/0.99  unary                                   12
% 3.23/0.99  binary                                  16
% 3.23/0.99  lits                                    107
% 3.23/0.99  lits eq                                 49
% 3.23/0.99  fd_pure                                 0
% 3.23/0.99  fd_pseudo                               0
% 3.23/0.99  fd_cond                                 4
% 3.23/0.99  fd_pseudo_cond                          0
% 3.23/0.99  AC symbols                              0
% 3.23/0.99  
% 3.23/0.99  ------ Schedule dynamic 5 is on 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ 
% 3.23/0.99  Current options:
% 3.23/0.99  ------ 
% 3.23/0.99  
% 3.23/0.99  ------ Input Options
% 3.23/0.99  
% 3.23/0.99  --out_options                           all
% 3.23/0.99  --tptp_safe_out                         true
% 3.23/0.99  --problem_path                          ""
% 3.23/0.99  --include_path                          ""
% 3.23/0.99  --clausifier                            res/vclausify_rel
% 3.23/0.99  --clausifier_options                    --mode clausify
% 3.23/0.99  --stdin                                 false
% 3.23/0.99  --stats_out                             all
% 3.23/0.99  
% 3.23/0.99  ------ General Options
% 3.23/0.99  
% 3.23/0.99  --fof                                   false
% 3.23/0.99  --time_out_real                         305.
% 3.23/0.99  --time_out_virtual                      -1.
% 3.23/0.99  --symbol_type_check                     false
% 3.23/0.99  --clausify_out                          false
% 3.23/0.99  --sig_cnt_out                           false
% 3.23/0.99  --trig_cnt_out                          false
% 3.23/0.99  --trig_cnt_out_tolerance                1.
% 3.23/0.99  --trig_cnt_out_sk_spl                   false
% 3.23/0.99  --abstr_cl_out                          false
% 3.23/0.99  
% 3.23/0.99  ------ Global Options
% 3.23/0.99  
% 3.23/0.99  --schedule                              default
% 3.23/0.99  --add_important_lit                     false
% 3.23/0.99  --prop_solver_per_cl                    1000
% 3.23/0.99  --min_unsat_core                        false
% 3.23/0.99  --soft_assumptions                      false
% 3.23/0.99  --soft_lemma_size                       3
% 3.23/0.99  --prop_impl_unit_size                   0
% 3.23/0.99  --prop_impl_unit                        []
% 3.23/0.99  --share_sel_clauses                     true
% 3.23/0.99  --reset_solvers                         false
% 3.23/0.99  --bc_imp_inh                            [conj_cone]
% 3.23/0.99  --conj_cone_tolerance                   3.
% 3.23/0.99  --extra_neg_conj                        none
% 3.23/0.99  --large_theory_mode                     true
% 3.23/0.99  --prolific_symb_bound                   200
% 3.23/0.99  --lt_threshold                          2000
% 3.23/0.99  --clause_weak_htbl                      true
% 3.23/0.99  --gc_record_bc_elim                     false
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing Options
% 3.23/0.99  
% 3.23/0.99  --preprocessing_flag                    true
% 3.23/0.99  --time_out_prep_mult                    0.1
% 3.23/0.99  --splitting_mode                        input
% 3.23/0.99  --splitting_grd                         true
% 3.23/0.99  --splitting_cvd                         false
% 3.23/0.99  --splitting_cvd_svl                     false
% 3.23/0.99  --splitting_nvd                         32
% 3.23/0.99  --sub_typing                            true
% 3.23/0.99  --prep_gs_sim                           true
% 3.23/0.99  --prep_unflatten                        true
% 3.23/0.99  --prep_res_sim                          true
% 3.23/0.99  --prep_upred                            true
% 3.23/0.99  --prep_sem_filter                       exhaustive
% 3.23/0.99  --prep_sem_filter_out                   false
% 3.23/0.99  --pred_elim                             true
% 3.23/0.99  --res_sim_input                         true
% 3.23/0.99  --eq_ax_congr_red                       true
% 3.23/0.99  --pure_diseq_elim                       true
% 3.23/0.99  --brand_transform                       false
% 3.23/0.99  --non_eq_to_eq                          false
% 3.23/0.99  --prep_def_merge                        true
% 3.23/0.99  --prep_def_merge_prop_impl              false
% 3.23/0.99  --prep_def_merge_mbd                    true
% 3.23/0.99  --prep_def_merge_tr_red                 false
% 3.23/0.99  --prep_def_merge_tr_cl                  false
% 3.23/0.99  --smt_preprocessing                     true
% 3.23/0.99  --smt_ac_axioms                         fast
% 3.23/0.99  --preprocessed_out                      false
% 3.23/0.99  --preprocessed_stats                    false
% 3.23/0.99  
% 3.23/0.99  ------ Abstraction refinement Options
% 3.23/0.99  
% 3.23/0.99  --abstr_ref                             []
% 3.23/0.99  --abstr_ref_prep                        false
% 3.23/0.99  --abstr_ref_until_sat                   false
% 3.23/0.99  --abstr_ref_sig_restrict                funpre
% 3.23/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.99  --abstr_ref_under                       []
% 3.23/0.99  
% 3.23/0.99  ------ SAT Options
% 3.23/0.99  
% 3.23/0.99  --sat_mode                              false
% 3.23/0.99  --sat_fm_restart_options                ""
% 3.23/0.99  --sat_gr_def                            false
% 3.23/0.99  --sat_epr_types                         true
% 3.23/0.99  --sat_non_cyclic_types                  false
% 3.23/0.99  --sat_finite_models                     false
% 3.23/0.99  --sat_fm_lemmas                         false
% 3.23/0.99  --sat_fm_prep                           false
% 3.23/0.99  --sat_fm_uc_incr                        true
% 3.23/0.99  --sat_out_model                         small
% 3.23/0.99  --sat_out_clauses                       false
% 3.23/0.99  
% 3.23/0.99  ------ QBF Options
% 3.23/0.99  
% 3.23/0.99  --qbf_mode                              false
% 3.23/0.99  --qbf_elim_univ                         false
% 3.23/0.99  --qbf_dom_inst                          none
% 3.23/0.99  --qbf_dom_pre_inst                      false
% 3.23/0.99  --qbf_sk_in                             false
% 3.23/0.99  --qbf_pred_elim                         true
% 3.23/0.99  --qbf_split                             512
% 3.23/0.99  
% 3.23/0.99  ------ BMC1 Options
% 3.23/0.99  
% 3.23/0.99  --bmc1_incremental                      false
% 3.23/0.99  --bmc1_axioms                           reachable_all
% 3.23/0.99  --bmc1_min_bound                        0
% 3.23/0.99  --bmc1_max_bound                        -1
% 3.23/0.99  --bmc1_max_bound_default                -1
% 3.23/0.99  --bmc1_symbol_reachability              true
% 3.23/0.99  --bmc1_property_lemmas                  false
% 3.23/0.99  --bmc1_k_induction                      false
% 3.23/0.99  --bmc1_non_equiv_states                 false
% 3.23/0.99  --bmc1_deadlock                         false
% 3.23/0.99  --bmc1_ucm                              false
% 3.23/0.99  --bmc1_add_unsat_core                   none
% 3.23/0.99  --bmc1_unsat_core_children              false
% 3.23/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.99  --bmc1_out_stat                         full
% 3.23/0.99  --bmc1_ground_init                      false
% 3.23/0.99  --bmc1_pre_inst_next_state              false
% 3.23/0.99  --bmc1_pre_inst_state                   false
% 3.23/0.99  --bmc1_pre_inst_reach_state             false
% 3.23/0.99  --bmc1_out_unsat_core                   false
% 3.23/0.99  --bmc1_aig_witness_out                  false
% 3.23/0.99  --bmc1_verbose                          false
% 3.23/0.99  --bmc1_dump_clauses_tptp                false
% 3.23/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.99  --bmc1_dump_file                        -
% 3.23/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.99  --bmc1_ucm_extend_mode                  1
% 3.23/0.99  --bmc1_ucm_init_mode                    2
% 3.23/0.99  --bmc1_ucm_cone_mode                    none
% 3.23/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.99  --bmc1_ucm_relax_model                  4
% 3.23/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.99  --bmc1_ucm_layered_model                none
% 3.23/0.99  --bmc1_ucm_max_lemma_size               10
% 3.23/0.99  
% 3.23/0.99  ------ AIG Options
% 3.23/0.99  
% 3.23/0.99  --aig_mode                              false
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation Options
% 3.23/0.99  
% 3.23/0.99  --instantiation_flag                    true
% 3.23/0.99  --inst_sos_flag                         false
% 3.23/0.99  --inst_sos_phase                        true
% 3.23/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.99  --inst_lit_sel_side                     none
% 3.23/0.99  --inst_solver_per_active                1400
% 3.23/0.99  --inst_solver_calls_frac                1.
% 3.23/0.99  --inst_passive_queue_type               priority_queues
% 3.23/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.99  --inst_passive_queues_freq              [25;2]
% 3.23/0.99  --inst_dismatching                      true
% 3.23/0.99  --inst_eager_unprocessed_to_passive     true
% 3.23/0.99  --inst_prop_sim_given                   true
% 3.23/0.99  --inst_prop_sim_new                     false
% 3.23/0.99  --inst_subs_new                         false
% 3.23/0.99  --inst_eq_res_simp                      false
% 3.23/0.99  --inst_subs_given                       false
% 3.23/0.99  --inst_orphan_elimination               true
% 3.23/0.99  --inst_learning_loop_flag               true
% 3.23/0.99  --inst_learning_start                   3000
% 3.23/0.99  --inst_learning_factor                  2
% 3.23/0.99  --inst_start_prop_sim_after_learn       3
% 3.23/0.99  --inst_sel_renew                        solver
% 3.23/0.99  --inst_lit_activity_flag                true
% 3.23/0.99  --inst_restr_to_given                   false
% 3.23/0.99  --inst_activity_threshold               500
% 3.23/0.99  --inst_out_proof                        true
% 3.23/0.99  
% 3.23/0.99  ------ Resolution Options
% 3.23/0.99  
% 3.23/0.99  --resolution_flag                       false
% 3.23/0.99  --res_lit_sel                           adaptive
% 3.23/0.99  --res_lit_sel_side                      none
% 3.23/0.99  --res_ordering                          kbo
% 3.23/0.99  --res_to_prop_solver                    active
% 3.23/0.99  --res_prop_simpl_new                    false
% 3.23/0.99  --res_prop_simpl_given                  true
% 3.23/0.99  --res_passive_queue_type                priority_queues
% 3.23/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.99  --res_passive_queues_freq               [15;5]
% 3.23/0.99  --res_forward_subs                      full
% 3.23/0.99  --res_backward_subs                     full
% 3.23/0.99  --res_forward_subs_resolution           true
% 3.23/0.99  --res_backward_subs_resolution          true
% 3.23/0.99  --res_orphan_elimination                true
% 3.23/0.99  --res_time_limit                        2.
% 3.23/0.99  --res_out_proof                         true
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Options
% 3.23/0.99  
% 3.23/0.99  --superposition_flag                    true
% 3.23/0.99  --sup_passive_queue_type                priority_queues
% 3.23/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.99  --demod_completeness_check              fast
% 3.23/0.99  --demod_use_ground                      true
% 3.23/0.99  --sup_to_prop_solver                    passive
% 3.23/0.99  --sup_prop_simpl_new                    true
% 3.23/0.99  --sup_prop_simpl_given                  true
% 3.23/0.99  --sup_fun_splitting                     false
% 3.23/0.99  --sup_smt_interval                      50000
% 3.23/0.99  
% 3.23/0.99  ------ Superposition Simplification Setup
% 3.23/0.99  
% 3.23/0.99  --sup_indices_passive                   []
% 3.23/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_full_bw                           [BwDemod]
% 3.23/0.99  --sup_immed_triv                        [TrivRules]
% 3.23/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_immed_bw_main                     []
% 3.23/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.99  
% 3.23/0.99  ------ Combination Options
% 3.23/0.99  
% 3.23/0.99  --comb_res_mult                         3
% 3.23/0.99  --comb_sup_mult                         2
% 3.23/0.99  --comb_inst_mult                        10
% 3.23/0.99  
% 3.23/0.99  ------ Debug Options
% 3.23/0.99  
% 3.23/0.99  --dbg_backtrace                         false
% 3.23/0.99  --dbg_dump_prop_clauses                 false
% 3.23/0.99  --dbg_dump_prop_clauses_file            -
% 3.23/0.99  --dbg_out_stat                          false
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  ------ Proving...
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS status Theorem for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  fof(f21,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f51,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f21])).
% 3.23/0.99  
% 3.23/0.99  fof(f52,plain,(
% 3.23/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(flattening,[],[f51])).
% 3.23/0.99  
% 3.23/0.99  fof(f59,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(nnf_transformation,[],[f52])).
% 3.23/0.99  
% 3.23/0.99  fof(f88,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f59])).
% 3.23/0.99  
% 3.23/0.99  fof(f24,conjecture,(
% 3.23/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f25,negated_conjecture,(
% 3.23/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.23/0.99    inference(negated_conjecture,[],[f24])).
% 3.23/0.99  
% 3.23/0.99  fof(f55,plain,(
% 3.23/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.23/0.99    inference(ennf_transformation,[],[f25])).
% 3.23/0.99  
% 3.23/0.99  fof(f56,plain,(
% 3.23/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.23/0.99    inference(flattening,[],[f55])).
% 3.23/0.99  
% 3.23/0.99  fof(f62,plain,(
% 3.23/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.23/0.99    introduced(choice_axiom,[])).
% 3.23/0.99  
% 3.23/0.99  fof(f63,plain,(
% 3.23/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.23/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f56,f62])).
% 3.23/0.99  
% 3.23/0.99  fof(f103,plain,(
% 3.23/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f104,plain,(
% 3.23/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f19,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f49,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f19])).
% 3.23/0.99  
% 3.23/0.99  fof(f86,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f49])).
% 3.23/0.99  
% 3.23/0.99  fof(f16,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f46,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f16])).
% 3.23/0.99  
% 3.23/0.99  fof(f83,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f46])).
% 3.23/0.99  
% 3.23/0.99  fof(f15,axiom,(
% 3.23/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f44,plain,(
% 3.23/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/0.99    inference(ennf_transformation,[],[f15])).
% 3.23/0.99  
% 3.23/0.99  fof(f45,plain,(
% 3.23/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(flattening,[],[f44])).
% 3.23/0.99  
% 3.23/0.99  fof(f82,plain,(
% 3.23/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f45])).
% 3.23/0.99  
% 3.23/0.99  fof(f105,plain,(
% 3.23/0.99    v2_funct_1(sK3)),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f102,plain,(
% 3.23/0.99    v1_funct_1(sK3)),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f23,axiom,(
% 3.23/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f53,plain,(
% 3.23/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/0.99    inference(ennf_transformation,[],[f23])).
% 3.23/0.99  
% 3.23/0.99  fof(f54,plain,(
% 3.23/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(flattening,[],[f53])).
% 3.23/0.99  
% 3.23/0.99  fof(f101,plain,(
% 3.23/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f54])).
% 3.23/0.99  
% 3.23/0.99  fof(f20,axiom,(
% 3.23/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f50,plain,(
% 3.23/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.99    inference(ennf_transformation,[],[f20])).
% 3.23/0.99  
% 3.23/0.99  fof(f87,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f50])).
% 3.23/0.99  
% 3.23/0.99  fof(f106,plain,(
% 3.23/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f81,plain,(
% 3.23/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f45])).
% 3.23/0.99  
% 3.23/0.99  fof(f12,axiom,(
% 3.23/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f38,plain,(
% 3.23/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.23/0.99    inference(ennf_transformation,[],[f12])).
% 3.23/0.99  
% 3.23/0.99  fof(f39,plain,(
% 3.23/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.23/0.99    inference(flattening,[],[f38])).
% 3.23/0.99  
% 3.23/0.99  fof(f78,plain,(
% 3.23/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f39])).
% 3.23/0.99  
% 3.23/0.99  fof(f77,plain,(
% 3.23/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f39])).
% 3.23/0.99  
% 3.23/0.99  fof(f100,plain,(
% 3.23/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f54])).
% 3.23/0.99  
% 3.23/0.99  fof(f107,plain,(
% 3.23/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.23/0.99    inference(cnf_transformation,[],[f63])).
% 3.23/0.99  
% 3.23/0.99  fof(f4,axiom,(
% 3.23/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f57,plain,(
% 3.23/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.99    inference(nnf_transformation,[],[f4])).
% 3.23/0.99  
% 3.23/0.99  fof(f58,plain,(
% 3.23/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.99    inference(flattening,[],[f57])).
% 3.23/0.99  
% 3.23/0.99  fof(f68,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.23/0.99    inference(cnf_transformation,[],[f58])).
% 3.23/0.99  
% 3.23/0.99  fof(f109,plain,(
% 3.23/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.23/0.99    inference(equality_resolution,[],[f68])).
% 3.23/0.99  
% 3.23/0.99  fof(f5,axiom,(
% 3.23/0.99    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f30,plain,(
% 3.23/0.99    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f5])).
% 3.23/0.99  
% 3.23/0.99  fof(f70,plain,(
% 3.23/0.99    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f30])).
% 3.23/0.99  
% 3.23/0.99  fof(f69,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.23/0.99    inference(cnf_transformation,[],[f58])).
% 3.23/0.99  
% 3.23/0.99  fof(f108,plain,(
% 3.23/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.23/0.99    inference(equality_resolution,[],[f69])).
% 3.23/0.99  
% 3.23/0.99  fof(f1,axiom,(
% 3.23/0.99    v1_xboole_0(k1_xboole_0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f64,plain,(
% 3.23/0.99    v1_xboole_0(k1_xboole_0)),
% 3.23/0.99    inference(cnf_transformation,[],[f1])).
% 3.23/0.99  
% 3.23/0.99  fof(f2,axiom,(
% 3.23/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f29,plain,(
% 3.23/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f2])).
% 3.23/0.99  
% 3.23/0.99  fof(f65,plain,(
% 3.23/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f29])).
% 3.23/0.99  
% 3.23/0.99  fof(f18,axiom,(
% 3.23/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.23/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.99  
% 3.23/0.99  fof(f48,plain,(
% 3.23/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.23/0.99    inference(ennf_transformation,[],[f18])).
% 3.23/0.99  
% 3.23/0.99  fof(f85,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f48])).
% 3.23/0.99  
% 3.23/0.99  fof(f91,plain,(
% 3.23/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.99    inference(cnf_transformation,[],[f59])).
% 3.23/0.99  
% 3.23/0.99  fof(f113,plain,(
% 3.23/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.23/0.99    inference(equality_resolution,[],[f91])).
% 3.23/0.99  
% 3.23/0.99  fof(f67,plain,(
% 3.23/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.23/0.99    inference(cnf_transformation,[],[f58])).
% 3.23/0.99  
% 3.23/0.99  cnf(c_29,plain,
% 3.23/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.23/0.99      | k1_xboole_0 = X2 ),
% 3.23/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_42,negated_conjecture,
% 3.23/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.23/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_801,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.23/0.99      | sK1 != X1
% 3.23/0.99      | sK2 != X2
% 3.23/0.99      | sK3 != X0
% 3.23/0.99      | k1_xboole_0 = X2 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_29,c_42]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_802,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.23/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.23/0.99      | k1_xboole_0 = sK2 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_801]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_41,negated_conjecture,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.23/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_804,plain,
% 3.23/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_802,c_41]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1558,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_22,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1564,plain,
% 3.23/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.23/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4048,plain,
% 3.23/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1558,c_1564]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4333,plain,
% 3.23/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_804,c_4048]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_19,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1566,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2809,plain,
% 3.23/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1558,c_1566]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_17,plain,
% 3.23/0.99      ( ~ v2_funct_1(X0)
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_40,negated_conjecture,
% 3.23/0.99      ( v2_funct_1(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_529,plain,
% 3.23/0.99      ( ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.23/0.99      | sK3 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_530,plain,
% 3.23/0.99      ( ~ v1_funct_1(sK3)
% 3.23/0.99      | ~ v1_relat_1(sK3)
% 3.23/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_529]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_43,negated_conjecture,
% 3.23/0.99      ( v1_funct_1(sK3) ),
% 3.23/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_532,plain,
% 3.23/0.99      ( ~ v1_relat_1(sK3)
% 3.23/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_530,c_43]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1552,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.23/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2829,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2809,c_1552]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_35,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1559,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.23/0.99      | v1_funct_1(X0) != iProver_top
% 3.23/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3928,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.23/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2829,c_1559]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_23,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1563,plain,
% 3.23/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.23/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3189,plain,
% 3.23/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1558,c_1563]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_39,negated_conjecture,
% 3.23/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.23/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3204,plain,
% 3.23/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_3189,c_39]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_18,plain,
% 3.23/0.99      ( ~ v2_funct_1(X0)
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_515,plain,
% 3.23/0.99      ( ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.23/0.99      | sK3 != X0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_40]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_516,plain,
% 3.23/0.99      ( ~ v1_funct_1(sK3)
% 3.23/0.99      | ~ v1_relat_1(sK3)
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_515]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_518,plain,
% 3.23/0.99      ( ~ v1_relat_1(sK3)
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_516,c_43]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1553,plain,
% 3.23/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.23/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2828,plain,
% 3.23/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_2809,c_1553]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3216,plain,
% 3.23/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_3204,c_2828]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3954,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.23/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_3928,c_3216]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_44,plain,
% 3.23/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_46,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_13,plain,
% 3.23/0.99      ( ~ v1_funct_1(X0)
% 3.23/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.23/0.99      | ~ v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1884,plain,
% 3.23/0.99      ( v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | ~ v1_funct_1(sK3)
% 3.23/0.99      | ~ v1_relat_1(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1885,plain,
% 3.23/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.23/0.99      | v1_funct_1(sK3) != iProver_top
% 3.23/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1884]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_14,plain,
% 3.23/0.99      ( ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1892,plain,
% 3.23/0.99      ( ~ v1_funct_1(sK3)
% 3.23/0.99      | v1_relat_1(k2_funct_1(sK3))
% 3.23/0.99      | ~ v1_relat_1(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1893,plain,
% 3.23/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.23/0.99      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.23/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1892]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1911,plain,
% 3.23/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.23/0.99      | v1_relat_1(sK3) ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1912,plain,
% 3.23/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.23/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5030,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_3954,c_44,c_46,c_1885,c_1893,c_1912]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5037,plain,
% 3.23/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_5030,c_1564]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5054,plain,
% 3.23/0.99      ( k1_relset_1(sK2,k1_relat_1(sK3),k2_funct_1(sK3)) = sK2 ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_5037,c_3216]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5138,plain,
% 3.23/0.99      ( k1_relset_1(sK2,sK1,k2_funct_1(sK3)) = sK2 | sK2 = k1_xboole_0 ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_4333,c_5054]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_36,plain,
% 3.23/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_relat_1(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_38,negated_conjecture,
% 3.23/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.23/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.23/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_825,plain,
% 3.23/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ v1_funct_1(X0)
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | ~ v1_relat_1(X0)
% 3.23/0.99      | k2_funct_1(sK3) != X0
% 3.23/0.99      | k2_relat_1(X0) != sK1
% 3.23/0.99      | k1_relat_1(X0) != sK2 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_36,c_38]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_826,plain,
% 3.23/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.23/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_825]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_838,plain,
% 3.23/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.23/0.99      inference(forward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_826,c_19]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1540,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_838]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_827,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.23/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_826]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2148,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.23/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_1540,c_44,c_46,c_827,c_1885,c_1893,c_1912]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2149,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_2148]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2950,plain,
% 3.23/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.23/0.99      | k2_relat_1(sK3) != sK2
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_2828,c_2149]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3014,plain,
% 3.23/0.99      ( k2_relat_1(sK3) != sK2
% 3.23/0.99      | k1_relat_1(sK3) != sK1
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_2950,c_2829]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3213,plain,
% 3.23/0.99      ( k1_relat_1(sK3) != sK1
% 3.23/0.99      | sK2 != sK2
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_3204,c_3014]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3228,plain,
% 3.23/0.99      ( k1_relat_1(sK3) != sK1
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(equality_resolution_simp,[status(thm)],[c_3213]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4606,plain,
% 3.23/0.99      ( sK2 = k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_4333,c_3228]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5035,plain,
% 3.23/0.99      ( sK2 = k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_4333,c_5030]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5139,plain,
% 3.23/0.99      ( sK2 = k1_xboole_0 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5138,c_4606,c_5035]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5143,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5139,c_5030]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4,plain,
% 3.23/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5248,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5143,c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4051,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.23/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_4,c_1564]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5545,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK3)) = k1_relat_1(k2_funct_1(sK3)) ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_5248,c_4051]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.23/0.99      | ~ v1_xboole_0(X1)
% 3.23/0.99      | v1_xboole_0(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1572,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/0.99      | v1_xboole_0(X1) != iProver_top
% 3.23/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_4796,plain,
% 3.23/0.99      ( v1_xboole_0(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_1558,c_1572]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5146,plain,
% 3.23/0.99      ( v1_xboole_0(k2_zfmisc_1(sK1,k1_xboole_0)) != iProver_top
% 3.23/0.99      | v1_xboole_0(sK3) = iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5139,c_4796]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_3,plain,
% 3.23/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5241,plain,
% 3.23/0.99      ( v1_xboole_0(sK3) = iProver_top
% 3.23/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5146,c_3]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_0,plain,
% 3.23/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_147,plain,
% 3.23/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5737,plain,
% 3.23/0.99      ( v1_xboole_0(sK3) = iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5241,c_147]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1,plain,
% 3.23/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1573,plain,
% 3.23/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5742,plain,
% 3.23/0.99      ( sK3 = k1_xboole_0 ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_5737,c_1573]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_21,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.99      | ~ v1_xboole_0(X2)
% 3.23/0.99      | v1_xboole_0(X0) ),
% 3.23/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1565,plain,
% 3.23/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.23/0.99      | v1_xboole_0(X2) != iProver_top
% 3.23/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5039,plain,
% 3.23/0.99      ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
% 3.23/0.99      | v1_xboole_0(k1_relat_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_5030,c_1565]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5542,plain,
% 3.23/0.99      ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top
% 3.23/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_5248,c_1572]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8381,plain,
% 3.23/0.99      ( v1_xboole_0(k2_funct_1(sK3)) = iProver_top ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5039,c_147,c_5542]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8385,plain,
% 3.23/0.99      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_8381,c_5742]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8388,plain,
% 3.23/0.99      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(superposition,[status(thm)],[c_8385,c_1573]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5157,plain,
% 3.23/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5139,c_3216]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_6329,plain,
% 3.23/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5742,c_5157]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_8517,plain,
% 3.23/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_8388,c_6329]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_9230,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,X0,k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(light_normalisation,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5545,c_5742,c_8388,c_8517]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_26,plain,
% 3.23/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.23/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.23/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.23/0.99      inference(cnf_transformation,[],[f113]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_718,plain,
% 3.23/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.23/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.23/0.99      | k2_funct_1(sK3) != X0
% 3.23/0.99      | sK1 != X1
% 3.23/0.99      | sK2 != k1_xboole_0 ),
% 3.23/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_38]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_719,plain,
% 3.23/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.23/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.23/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.23/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | sK2 != k1_xboole_0 ),
% 3.23/0.99      inference(unflattening,[status(thm)],[c_718]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1545,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | sK2 != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_1783,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | sK2 != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.23/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_1545,c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2237,plain,
% 3.23/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | sK2 != k1_xboole_0
% 3.23/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.23/0.99      inference(global_propositional_subsumption,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_1783,c_44,c_46,c_1885,c_1912]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_2238,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | sK2 != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/0.99      inference(renaming,[status(thm)],[c_2237]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5160,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5139,c_2238]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5199,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/0.99      inference(equality_resolution_simp,[status(thm)],[c_5160]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5203,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.23/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_5199,c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5251,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0 ),
% 3.23/0.99      inference(backward_subsumption_resolution,
% 3.23/0.99                [status(thm)],
% 3.23/0.99                [c_5248,c_5203]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_9197,plain,
% 3.23/0.99      ( k1_relset_1(k1_xboole_0,sK1,k1_xboole_0) != k1_xboole_0 ),
% 3.23/0.99      inference(light_normalisation,[status(thm)],[c_5251,c_5742,c_8388]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_9232,plain,
% 3.23/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.23/0.99      inference(demodulation,[status(thm)],[c_9230,c_9197]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_140,plain,
% 3.23/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_5,plain,
% 3.23/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 = X0
% 3.23/0.99      | k1_xboole_0 = X1 ),
% 3.23/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(c_139,plain,
% 3.23/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.23/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.23/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.23/0.99  
% 3.23/0.99  cnf(contradiction,plain,
% 3.23/0.99      ( $false ),
% 3.23/0.99      inference(minisat,[status(thm)],[c_9232,c_140,c_139]) ).
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.99  
% 3.23/0.99  ------                               Statistics
% 3.23/0.99  
% 3.23/0.99  ------ General
% 3.23/0.99  
% 3.23/0.99  abstr_ref_over_cycles:                  0
% 3.23/0.99  abstr_ref_under_cycles:                 0
% 3.23/0.99  gc_basic_clause_elim:                   0
% 3.23/0.99  forced_gc_time:                         0
% 3.23/0.99  parsing_time:                           0.044
% 3.23/0.99  unif_index_cands_time:                  0.
% 3.23/0.99  unif_index_add_time:                    0.
% 3.23/0.99  orderings_time:                         0.
% 3.23/0.99  out_proof_time:                         0.014
% 3.23/0.99  total_time:                             0.286
% 3.23/0.99  num_of_symbols:                         54
% 3.23/0.99  num_of_terms:                           7004
% 3.23/0.99  
% 3.23/0.99  ------ Preprocessing
% 3.23/0.99  
% 3.23/0.99  num_of_splits:                          0
% 3.23/0.99  num_of_split_atoms:                     0
% 3.23/0.99  num_of_reused_defs:                     0
% 3.23/0.99  num_eq_ax_congr_red:                    8
% 3.23/0.99  num_of_sem_filtered_clauses:            1
% 3.23/0.99  num_of_subtypes:                        0
% 3.23/0.99  monotx_restored_types:                  0
% 3.23/0.99  sat_num_of_epr_types:                   0
% 3.23/0.99  sat_num_of_non_cyclic_types:            0
% 3.23/0.99  sat_guarded_non_collapsed_types:        0
% 3.23/0.99  num_pure_diseq_elim:                    0
% 3.23/0.99  simp_replaced_by:                       0
% 3.23/0.99  res_preprocessed:                       168
% 3.23/0.99  prep_upred:                             0
% 3.23/0.99  prep_unflattend:                        62
% 3.23/0.99  smt_new_axioms:                         0
% 3.23/0.99  pred_elim_cands:                        8
% 3.23/0.99  pred_elim:                              4
% 3.23/0.99  pred_elim_cl:                           -2
% 3.23/0.99  pred_elim_cycles:                       5
% 3.23/0.99  merged_defs:                            0
% 3.23/0.99  merged_defs_ncl:                        0
% 3.23/0.99  bin_hyper_res:                          0
% 3.23/0.99  prep_cycles:                            3
% 3.23/0.99  pred_elim_time:                         0.01
% 3.23/0.99  splitting_time:                         0.
% 3.23/0.99  sem_filter_time:                        0.
% 3.23/0.99  monotx_time:                            0.
% 3.23/0.99  subtype_inf_time:                       0.
% 3.23/0.99  
% 3.23/0.99  ------ Problem properties
% 3.23/0.99  
% 3.23/0.99  clauses:                                45
% 3.23/0.99  conjectures:                            3
% 3.23/0.99  epr:                                    3
% 3.23/0.99  horn:                                   38
% 3.23/0.99  ground:                                 15
% 3.23/0.99  unary:                                  12
% 3.23/0.99  binary:                                 16
% 3.23/0.99  lits:                                   107
% 3.23/0.99  lits_eq:                                49
% 3.23/0.99  fd_pure:                                0
% 3.23/0.99  fd_pseudo:                              0
% 3.23/0.99  fd_cond:                                4
% 3.23/0.99  fd_pseudo_cond:                         0
% 3.23/0.99  ac_symbols:                             0
% 3.23/0.99  
% 3.23/0.99  ------ Propositional Solver
% 3.23/0.99  
% 3.23/0.99  prop_solver_calls:                      24
% 3.23/0.99  prop_fast_solver_calls:                 1253
% 3.23/0.99  smt_solver_calls:                       0
% 3.23/0.99  smt_fast_solver_calls:                  0
% 3.23/0.99  prop_num_of_clauses:                    3117
% 3.23/0.99  prop_preprocess_simplified:             9403
% 3.23/0.99  prop_fo_subsumed:                       40
% 3.23/0.99  prop_solver_time:                       0.
% 3.23/0.99  smt_solver_time:                        0.
% 3.23/0.99  smt_fast_solver_time:                   0.
% 3.23/0.99  prop_fast_solver_time:                  0.
% 3.23/0.99  prop_unsat_core_time:                   0.
% 3.23/0.99  
% 3.23/0.99  ------ QBF
% 3.23/0.99  
% 3.23/0.99  qbf_q_res:                              0
% 3.23/0.99  qbf_num_tautologies:                    0
% 3.23/0.99  qbf_prep_cycles:                        0
% 3.23/0.99  
% 3.23/0.99  ------ BMC1
% 3.23/0.99  
% 3.23/0.99  bmc1_current_bound:                     -1
% 3.23/0.99  bmc1_last_solved_bound:                 -1
% 3.23/0.99  bmc1_unsat_core_size:                   -1
% 3.23/0.99  bmc1_unsat_core_parents_size:           -1
% 3.23/0.99  bmc1_merge_next_fun:                    0
% 3.23/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.23/0.99  
% 3.23/0.99  ------ Instantiation
% 3.23/0.99  
% 3.23/0.99  inst_num_of_clauses:                    1204
% 3.23/0.99  inst_num_in_passive:                    613
% 3.23/0.99  inst_num_in_active:                     493
% 3.23/0.99  inst_num_in_unprocessed:                98
% 3.23/0.99  inst_num_of_loops:                      690
% 3.23/0.99  inst_num_of_learning_restarts:          0
% 3.23/0.99  inst_num_moves_active_passive:          195
% 3.23/0.99  inst_lit_activity:                      0
% 3.23/0.99  inst_lit_activity_moves:                0
% 3.23/0.99  inst_num_tautologies:                   0
% 3.23/0.99  inst_num_prop_implied:                  0
% 3.23/0.99  inst_num_existing_simplified:           0
% 3.23/0.99  inst_num_eq_res_simplified:             0
% 3.23/0.99  inst_num_child_elim:                    0
% 3.23/0.99  inst_num_of_dismatching_blockings:      537
% 3.23/0.99  inst_num_of_non_proper_insts:           873
% 3.23/0.99  inst_num_of_duplicates:                 0
% 3.23/0.99  inst_inst_num_from_inst_to_res:         0
% 3.23/0.99  inst_dismatching_checking_time:         0.
% 3.23/0.99  
% 3.23/0.99  ------ Resolution
% 3.23/0.99  
% 3.23/0.99  res_num_of_clauses:                     0
% 3.23/0.99  res_num_in_passive:                     0
% 3.23/0.99  res_num_in_active:                      0
% 3.23/0.99  res_num_of_loops:                       171
% 3.23/0.99  res_forward_subset_subsumed:            56
% 3.23/0.99  res_backward_subset_subsumed:           0
% 3.23/0.99  res_forward_subsumed:                   0
% 3.23/0.99  res_backward_subsumed:                  0
% 3.23/0.99  res_forward_subsumption_resolution:     5
% 3.23/0.99  res_backward_subsumption_resolution:    1
% 3.23/0.99  res_clause_to_clause_subsumption:       365
% 3.23/0.99  res_orphan_elimination:                 0
% 3.23/0.99  res_tautology_del:                      115
% 3.23/0.99  res_num_eq_res_simplified:              0
% 3.23/0.99  res_num_sel_changes:                    0
% 3.23/0.99  res_moves_from_active_to_pass:          0
% 3.23/0.99  
% 3.23/0.99  ------ Superposition
% 3.23/0.99  
% 3.23/0.99  sup_time_total:                         0.
% 3.23/0.99  sup_time_generating:                    0.
% 3.23/0.99  sup_time_sim_full:                      0.
% 3.23/0.99  sup_time_sim_immed:                     0.
% 3.23/0.99  
% 3.23/0.99  sup_num_of_clauses:                     144
% 3.23/0.99  sup_num_in_active:                      61
% 3.23/0.99  sup_num_in_passive:                     83
% 3.23/0.99  sup_num_of_loops:                       137
% 3.23/0.99  sup_fw_superposition:                   115
% 3.23/0.99  sup_bw_superposition:                   109
% 3.23/0.99  sup_immediate_simplified:               91
% 3.23/0.99  sup_given_eliminated:                   0
% 3.23/0.99  comparisons_done:                       0
% 3.23/0.99  comparisons_avoided:                    11
% 3.23/0.99  
% 3.23/0.99  ------ Simplifications
% 3.23/0.99  
% 3.23/0.99  
% 3.23/0.99  sim_fw_subset_subsumed:                 22
% 3.23/0.99  sim_bw_subset_subsumed:                 8
% 3.23/0.99  sim_fw_subsumed:                        34
% 3.23/0.99  sim_bw_subsumed:                        2
% 3.23/0.99  sim_fw_subsumption_res:                 2
% 3.23/0.99  sim_bw_subsumption_res:                 4
% 3.23/0.99  sim_tautology_del:                      5
% 3.23/0.99  sim_eq_tautology_del:                   10
% 3.23/0.99  sim_eq_res_simp:                        3
% 3.23/0.99  sim_fw_demodulated:                     30
% 3.23/0.99  sim_bw_demodulated:                     72
% 3.23/0.99  sim_light_normalised:                   71
% 3.23/0.99  sim_joinable_taut:                      0
% 3.23/0.99  sim_joinable_simp:                      0
% 3.23/0.99  sim_ac_normalised:                      0
% 3.23/0.99  sim_smt_subsumption:                    0
% 3.23/0.99  
%------------------------------------------------------------------------------
