%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:14 EST 2020

% Result     : Theorem 38.97s
% Output     : CNFRefutation 38.97s
% Verified   : 
% Statistics : Number of formulae       :  232 (3366 expanded)
%              Number of clauses        :  136 ( 937 expanded)
%              Number of leaves         :   25 ( 903 expanded)
%              Depth                    :   21
%              Number of atoms          :  909 (26487 expanded)
%              Number of equality atoms :  435 (9825 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f109,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f82])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f107,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f60,f82])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f105,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f59,f82])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f110,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f82])).

fof(f58,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f58,f82])).

fof(f64,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f108,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f64,f82])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
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

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f56,plain,(
    ! [X2,X0,X1] :
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
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
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
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f56,f55])).

fof(f100,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f114,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f78,f82])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f99,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f57])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
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

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f97,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f102,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f33,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f71,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f112,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f71,f82])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f82])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f67,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f104,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_809,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_54494,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_91649,plain,
    ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_54494])).

cnf(c_815,plain,
    ( X0 != X1
    | k2_funct_1(X0) = k2_funct_1(X1) ),
    theory(equality)).

cnf(c_65355,plain,
    ( X0 != k2_funct_1(sK3)
    | k2_funct_1(X0) = k2_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_815])).

cnf(c_85173,plain,
    ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
    | sK2 != k2_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_65355])).

cnf(c_55772,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_56962,plain,
    ( X0 != sK2
    | sK2 = X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_55772])).

cnf(c_62034,plain,
    ( k2_funct_1(sK3) != sK2
    | sK2 = k2_funct_1(sK3)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_56962])).

cnf(c_1589,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1977,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1589])).

cnf(c_4825,plain,
    ( k2_funct_1(X0) != sK3
    | sK3 = k2_funct_1(X0)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1977])).

cnf(c_29544,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | sK3 = k2_funct_1(k2_funct_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_4825])).

cnf(c_6,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1430,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1434,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2628,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
    inference(superposition,[status(thm)],[c_1430,c_1434])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2629,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(light_normalisation,[status(thm)],[c_2628,c_0])).

cnf(c_10,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1428,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4419,plain,
    ( k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2629,c_1428])).

cnf(c_1,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4423,plain,
    ( k6_partfun1(X0) != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4419,c_1])).

cnf(c_4424,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4423])).

cnf(c_131,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_134,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_6396,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4424,c_131,c_134])).

cnf(c_19,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_38,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_38])).

cnf(c_494,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_20,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_502,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_494,c_20])).

cnf(c_1399,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_502])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1526,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2442,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1399,c_45,c_43,c_42,c_40,c_502,c_1526])).

cnf(c_39,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1415,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6311,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_39,c_1415])).

cnf(c_46,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_47,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_6389,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6311,c_46,c_47,c_48])).

cnf(c_6390,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_6389])).

cnf(c_6393,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2442,c_6390])).

cnf(c_49,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_50,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_51,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_36,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_808,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_839,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_1524,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1525,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_6465,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6393,c_49,c_50,c_51,c_36,c_839,c_1525])).

cnf(c_6466,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_6465])).

cnf(c_6469,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_6396,c_6466])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1424,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6590,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6469,c_1424])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1578,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1955,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1578])).

cnf(c_1956,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_13085,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6590,c_49,c_51,c_1956])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_506,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_38])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_598,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_507])).

cnf(c_1398,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_598])).

cnf(c_1991,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1398])).

cnf(c_2449,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1991,c_46,c_47,c_48,c_49,c_50,c_51])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1409,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4080,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2449,c_1409])).

cnf(c_12941,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4080,c_49,c_50,c_51,c_36,c_839,c_1525,c_6469])).

cnf(c_13087,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_13085,c_12941])).

cnf(c_13101,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_13087,c_0])).

cnf(c_13102,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_13101,c_0])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1423,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_12943,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12941,c_1423])).

cnf(c_1407,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1421,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2737,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1407,c_1421])).

cnf(c_2740,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2737,c_2449])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1427,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6591,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6469,c_1427])).

cnf(c_8061,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6591,c_49,c_51,c_1956])).

cnf(c_12945,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12943,c_2740,c_8061])).

cnf(c_12946,plain,
    ( ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(k2_funct_1(sK3)) != sK0
    | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12945])).

cnf(c_1404,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1417,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4504,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1407,c_1417])).

cnf(c_4590,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4504,c_49])).

cnf(c_4591,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4590])).

cnf(c_4598,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1404,c_4591])).

cnf(c_4599,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4598,c_2442])).

cnf(c_5237,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4599,c_46])).

cnf(c_5710,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5237,c_1423])).

cnf(c_2738,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1404,c_1421])).

cnf(c_2739,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2738,c_39])).

cnf(c_5715,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5710,c_2739,c_2740])).

cnf(c_5716,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5715])).

cnf(c_2350,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2351,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2350])).

cnf(c_11435,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5716,c_46,c_48,c_49,c_51,c_1956,c_2351,c_6469])).

cnf(c_11436,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_11435])).

cnf(c_9336,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_8631,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1426,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6592,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6469,c_1426])).

cnf(c_6593,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6592,c_2740])).

cnf(c_6470,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6469])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3843,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2645,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_808])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2331,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_34,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91649,c_85173,c_62034,c_29544,c_13102,c_13087,c_12946,c_11436,c_9336,c_8631,c_6593,c_6470,c_3843,c_2645,c_2331,c_1956,c_1955,c_34,c_51,c_40,c_49,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:33:05 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 38.97/5.50  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 38.97/5.50  
% 38.97/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 38.97/5.50  
% 38.97/5.50  ------  iProver source info
% 38.97/5.50  
% 38.97/5.50  git: date: 2020-06-30 10:37:57 +0100
% 38.97/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 38.97/5.50  git: non_committed_changes: false
% 38.97/5.50  git: last_make_outside_of_git: false
% 38.97/5.50  
% 38.97/5.50  ------ 
% 38.97/5.50  
% 38.97/5.50  ------ Input Options
% 38.97/5.50  
% 38.97/5.50  --out_options                           all
% 38.97/5.50  --tptp_safe_out                         true
% 38.97/5.50  --problem_path                          ""
% 38.97/5.50  --include_path                          ""
% 38.97/5.50  --clausifier                            res/vclausify_rel
% 38.97/5.50  --clausifier_options                    ""
% 38.97/5.50  --stdin                                 false
% 38.97/5.50  --stats_out                             all
% 38.97/5.50  
% 38.97/5.50  ------ General Options
% 38.97/5.50  
% 38.97/5.50  --fof                                   false
% 38.97/5.50  --time_out_real                         305.
% 38.97/5.50  --time_out_virtual                      -1.
% 38.97/5.50  --symbol_type_check                     false
% 38.97/5.50  --clausify_out                          false
% 38.97/5.50  --sig_cnt_out                           false
% 38.97/5.50  --trig_cnt_out                          false
% 38.97/5.50  --trig_cnt_out_tolerance                1.
% 38.97/5.50  --trig_cnt_out_sk_spl                   false
% 38.97/5.50  --abstr_cl_out                          false
% 38.97/5.50  
% 38.97/5.50  ------ Global Options
% 38.97/5.50  
% 38.97/5.50  --schedule                              default
% 38.97/5.50  --add_important_lit                     false
% 38.97/5.50  --prop_solver_per_cl                    1000
% 38.97/5.50  --min_unsat_core                        false
% 38.97/5.50  --soft_assumptions                      false
% 38.97/5.50  --soft_lemma_size                       3
% 38.97/5.50  --prop_impl_unit_size                   0
% 38.97/5.50  --prop_impl_unit                        []
% 38.97/5.50  --share_sel_clauses                     true
% 38.97/5.50  --reset_solvers                         false
% 38.97/5.50  --bc_imp_inh                            [conj_cone]
% 38.97/5.50  --conj_cone_tolerance                   3.
% 38.97/5.50  --extra_neg_conj                        none
% 38.97/5.50  --large_theory_mode                     true
% 38.97/5.50  --prolific_symb_bound                   200
% 38.97/5.50  --lt_threshold                          2000
% 38.97/5.50  --clause_weak_htbl                      true
% 38.97/5.50  --gc_record_bc_elim                     false
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing Options
% 38.97/5.50  
% 38.97/5.50  --preprocessing_flag                    true
% 38.97/5.50  --time_out_prep_mult                    0.1
% 38.97/5.50  --splitting_mode                        input
% 38.97/5.50  --splitting_grd                         true
% 38.97/5.50  --splitting_cvd                         false
% 38.97/5.50  --splitting_cvd_svl                     false
% 38.97/5.50  --splitting_nvd                         32
% 38.97/5.50  --sub_typing                            true
% 38.97/5.50  --prep_gs_sim                           true
% 38.97/5.50  --prep_unflatten                        true
% 38.97/5.50  --prep_res_sim                          true
% 38.97/5.50  --prep_upred                            true
% 38.97/5.50  --prep_sem_filter                       exhaustive
% 38.97/5.50  --prep_sem_filter_out                   false
% 38.97/5.50  --pred_elim                             true
% 38.97/5.50  --res_sim_input                         true
% 38.97/5.50  --eq_ax_congr_red                       true
% 38.97/5.50  --pure_diseq_elim                       true
% 38.97/5.50  --brand_transform                       false
% 38.97/5.50  --non_eq_to_eq                          false
% 38.97/5.50  --prep_def_merge                        true
% 38.97/5.50  --prep_def_merge_prop_impl              false
% 38.97/5.50  --prep_def_merge_mbd                    true
% 38.97/5.50  --prep_def_merge_tr_red                 false
% 38.97/5.50  --prep_def_merge_tr_cl                  false
% 38.97/5.50  --smt_preprocessing                     true
% 38.97/5.50  --smt_ac_axioms                         fast
% 38.97/5.50  --preprocessed_out                      false
% 38.97/5.50  --preprocessed_stats                    false
% 38.97/5.50  
% 38.97/5.50  ------ Abstraction refinement Options
% 38.97/5.50  
% 38.97/5.50  --abstr_ref                             []
% 38.97/5.50  --abstr_ref_prep                        false
% 38.97/5.50  --abstr_ref_until_sat                   false
% 38.97/5.50  --abstr_ref_sig_restrict                funpre
% 38.97/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 38.97/5.50  --abstr_ref_under                       []
% 38.97/5.50  
% 38.97/5.50  ------ SAT Options
% 38.97/5.50  
% 38.97/5.50  --sat_mode                              false
% 38.97/5.50  --sat_fm_restart_options                ""
% 38.97/5.50  --sat_gr_def                            false
% 38.97/5.50  --sat_epr_types                         true
% 38.97/5.50  --sat_non_cyclic_types                  false
% 38.97/5.50  --sat_finite_models                     false
% 38.97/5.50  --sat_fm_lemmas                         false
% 38.97/5.50  --sat_fm_prep                           false
% 38.97/5.50  --sat_fm_uc_incr                        true
% 38.97/5.50  --sat_out_model                         small
% 38.97/5.50  --sat_out_clauses                       false
% 38.97/5.50  
% 38.97/5.50  ------ QBF Options
% 38.97/5.50  
% 38.97/5.50  --qbf_mode                              false
% 38.97/5.50  --qbf_elim_univ                         false
% 38.97/5.50  --qbf_dom_inst                          none
% 38.97/5.50  --qbf_dom_pre_inst                      false
% 38.97/5.50  --qbf_sk_in                             false
% 38.97/5.50  --qbf_pred_elim                         true
% 38.97/5.50  --qbf_split                             512
% 38.97/5.50  
% 38.97/5.50  ------ BMC1 Options
% 38.97/5.50  
% 38.97/5.50  --bmc1_incremental                      false
% 38.97/5.50  --bmc1_axioms                           reachable_all
% 38.97/5.50  --bmc1_min_bound                        0
% 38.97/5.50  --bmc1_max_bound                        -1
% 38.97/5.50  --bmc1_max_bound_default                -1
% 38.97/5.50  --bmc1_symbol_reachability              true
% 38.97/5.50  --bmc1_property_lemmas                  false
% 38.97/5.50  --bmc1_k_induction                      false
% 38.97/5.50  --bmc1_non_equiv_states                 false
% 38.97/5.50  --bmc1_deadlock                         false
% 38.97/5.50  --bmc1_ucm                              false
% 38.97/5.50  --bmc1_add_unsat_core                   none
% 38.97/5.50  --bmc1_unsat_core_children              false
% 38.97/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 38.97/5.50  --bmc1_out_stat                         full
% 38.97/5.50  --bmc1_ground_init                      false
% 38.97/5.50  --bmc1_pre_inst_next_state              false
% 38.97/5.50  --bmc1_pre_inst_state                   false
% 38.97/5.50  --bmc1_pre_inst_reach_state             false
% 38.97/5.50  --bmc1_out_unsat_core                   false
% 38.97/5.50  --bmc1_aig_witness_out                  false
% 38.97/5.50  --bmc1_verbose                          false
% 38.97/5.50  --bmc1_dump_clauses_tptp                false
% 38.97/5.50  --bmc1_dump_unsat_core_tptp             false
% 38.97/5.50  --bmc1_dump_file                        -
% 38.97/5.50  --bmc1_ucm_expand_uc_limit              128
% 38.97/5.50  --bmc1_ucm_n_expand_iterations          6
% 38.97/5.50  --bmc1_ucm_extend_mode                  1
% 38.97/5.50  --bmc1_ucm_init_mode                    2
% 38.97/5.50  --bmc1_ucm_cone_mode                    none
% 38.97/5.50  --bmc1_ucm_reduced_relation_type        0
% 38.97/5.50  --bmc1_ucm_relax_model                  4
% 38.97/5.50  --bmc1_ucm_full_tr_after_sat            true
% 38.97/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 38.97/5.50  --bmc1_ucm_layered_model                none
% 38.97/5.50  --bmc1_ucm_max_lemma_size               10
% 38.97/5.50  
% 38.97/5.50  ------ AIG Options
% 38.97/5.50  
% 38.97/5.50  --aig_mode                              false
% 38.97/5.50  
% 38.97/5.50  ------ Instantiation Options
% 38.97/5.50  
% 38.97/5.50  --instantiation_flag                    true
% 38.97/5.50  --inst_sos_flag                         true
% 38.97/5.50  --inst_sos_phase                        true
% 38.97/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 38.97/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 38.97/5.50  --inst_lit_sel_side                     num_symb
% 38.97/5.50  --inst_solver_per_active                1400
% 38.97/5.50  --inst_solver_calls_frac                1.
% 38.97/5.50  --inst_passive_queue_type               priority_queues
% 38.97/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 38.97/5.50  --inst_passive_queues_freq              [25;2]
% 38.97/5.50  --inst_dismatching                      true
% 38.97/5.50  --inst_eager_unprocessed_to_passive     true
% 38.97/5.50  --inst_prop_sim_given                   true
% 38.97/5.50  --inst_prop_sim_new                     false
% 38.97/5.50  --inst_subs_new                         false
% 38.97/5.50  --inst_eq_res_simp                      false
% 38.97/5.50  --inst_subs_given                       false
% 38.97/5.50  --inst_orphan_elimination               true
% 38.97/5.50  --inst_learning_loop_flag               true
% 38.97/5.50  --inst_learning_start                   3000
% 38.97/5.50  --inst_learning_factor                  2
% 38.97/5.50  --inst_start_prop_sim_after_learn       3
% 38.97/5.50  --inst_sel_renew                        solver
% 38.97/5.50  --inst_lit_activity_flag                true
% 38.97/5.50  --inst_restr_to_given                   false
% 38.97/5.50  --inst_activity_threshold               500
% 38.97/5.50  --inst_out_proof                        true
% 38.97/5.50  
% 38.97/5.50  ------ Resolution Options
% 38.97/5.50  
% 38.97/5.50  --resolution_flag                       true
% 38.97/5.50  --res_lit_sel                           adaptive
% 38.97/5.50  --res_lit_sel_side                      none
% 38.97/5.50  --res_ordering                          kbo
% 38.97/5.50  --res_to_prop_solver                    active
% 38.97/5.50  --res_prop_simpl_new                    false
% 38.97/5.50  --res_prop_simpl_given                  true
% 38.97/5.50  --res_passive_queue_type                priority_queues
% 38.97/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 38.97/5.50  --res_passive_queues_freq               [15;5]
% 38.97/5.50  --res_forward_subs                      full
% 38.97/5.50  --res_backward_subs                     full
% 38.97/5.50  --res_forward_subs_resolution           true
% 38.97/5.50  --res_backward_subs_resolution          true
% 38.97/5.50  --res_orphan_elimination                true
% 38.97/5.50  --res_time_limit                        2.
% 38.97/5.50  --res_out_proof                         true
% 38.97/5.50  
% 38.97/5.50  ------ Superposition Options
% 38.97/5.50  
% 38.97/5.50  --superposition_flag                    true
% 38.97/5.50  --sup_passive_queue_type                priority_queues
% 38.97/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 38.97/5.50  --sup_passive_queues_freq               [8;1;4]
% 38.97/5.50  --demod_completeness_check              fast
% 38.97/5.50  --demod_use_ground                      true
% 38.97/5.50  --sup_to_prop_solver                    passive
% 38.97/5.50  --sup_prop_simpl_new                    true
% 38.97/5.50  --sup_prop_simpl_given                  true
% 38.97/5.50  --sup_fun_splitting                     true
% 38.97/5.50  --sup_smt_interval                      50000
% 38.97/5.50  
% 38.97/5.50  ------ Superposition Simplification Setup
% 38.97/5.50  
% 38.97/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 38.97/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 38.97/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 38.97/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 38.97/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 38.97/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 38.97/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 38.97/5.50  --sup_immed_triv                        [TrivRules]
% 38.97/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_immed_bw_main                     []
% 38.97/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 38.97/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 38.97/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_input_bw                          []
% 38.97/5.50  
% 38.97/5.50  ------ Combination Options
% 38.97/5.50  
% 38.97/5.50  --comb_res_mult                         3
% 38.97/5.50  --comb_sup_mult                         2
% 38.97/5.50  --comb_inst_mult                        10
% 38.97/5.50  
% 38.97/5.50  ------ Debug Options
% 38.97/5.50  
% 38.97/5.50  --dbg_backtrace                         false
% 38.97/5.50  --dbg_dump_prop_clauses                 false
% 38.97/5.50  --dbg_dump_prop_clauses_file            -
% 38.97/5.50  --dbg_out_stat                          false
% 38.97/5.50  ------ Parsing...
% 38.97/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 38.97/5.50  ------ Proving...
% 38.97/5.50  ------ Problem Properties 
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  clauses                                 43
% 38.97/5.50  conjectures                             11
% 38.97/5.50  EPR                                     7
% 38.97/5.50  Horn                                    39
% 38.97/5.50  unary                                   16
% 38.97/5.50  binary                                  4
% 38.97/5.50  lits                                    162
% 38.97/5.50  lits eq                                 36
% 38.97/5.50  fd_pure                                 0
% 38.97/5.50  fd_pseudo                               0
% 38.97/5.50  fd_cond                                 4
% 38.97/5.50  fd_pseudo_cond                          1
% 38.97/5.50  AC symbols                              0
% 38.97/5.50  
% 38.97/5.50  ------ Schedule dynamic 5 is on 
% 38.97/5.50  
% 38.97/5.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  ------ 
% 38.97/5.50  Current options:
% 38.97/5.50  ------ 
% 38.97/5.50  
% 38.97/5.50  ------ Input Options
% 38.97/5.50  
% 38.97/5.50  --out_options                           all
% 38.97/5.50  --tptp_safe_out                         true
% 38.97/5.50  --problem_path                          ""
% 38.97/5.50  --include_path                          ""
% 38.97/5.50  --clausifier                            res/vclausify_rel
% 38.97/5.50  --clausifier_options                    ""
% 38.97/5.50  --stdin                                 false
% 38.97/5.50  --stats_out                             all
% 38.97/5.50  
% 38.97/5.50  ------ General Options
% 38.97/5.50  
% 38.97/5.50  --fof                                   false
% 38.97/5.50  --time_out_real                         305.
% 38.97/5.50  --time_out_virtual                      -1.
% 38.97/5.50  --symbol_type_check                     false
% 38.97/5.50  --clausify_out                          false
% 38.97/5.50  --sig_cnt_out                           false
% 38.97/5.50  --trig_cnt_out                          false
% 38.97/5.50  --trig_cnt_out_tolerance                1.
% 38.97/5.50  --trig_cnt_out_sk_spl                   false
% 38.97/5.50  --abstr_cl_out                          false
% 38.97/5.50  
% 38.97/5.50  ------ Global Options
% 38.97/5.50  
% 38.97/5.50  --schedule                              default
% 38.97/5.50  --add_important_lit                     false
% 38.97/5.50  --prop_solver_per_cl                    1000
% 38.97/5.50  --min_unsat_core                        false
% 38.97/5.50  --soft_assumptions                      false
% 38.97/5.50  --soft_lemma_size                       3
% 38.97/5.50  --prop_impl_unit_size                   0
% 38.97/5.50  --prop_impl_unit                        []
% 38.97/5.50  --share_sel_clauses                     true
% 38.97/5.50  --reset_solvers                         false
% 38.97/5.50  --bc_imp_inh                            [conj_cone]
% 38.97/5.50  --conj_cone_tolerance                   3.
% 38.97/5.50  --extra_neg_conj                        none
% 38.97/5.50  --large_theory_mode                     true
% 38.97/5.50  --prolific_symb_bound                   200
% 38.97/5.50  --lt_threshold                          2000
% 38.97/5.50  --clause_weak_htbl                      true
% 38.97/5.50  --gc_record_bc_elim                     false
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing Options
% 38.97/5.50  
% 38.97/5.50  --preprocessing_flag                    true
% 38.97/5.50  --time_out_prep_mult                    0.1
% 38.97/5.50  --splitting_mode                        input
% 38.97/5.50  --splitting_grd                         true
% 38.97/5.50  --splitting_cvd                         false
% 38.97/5.50  --splitting_cvd_svl                     false
% 38.97/5.50  --splitting_nvd                         32
% 38.97/5.50  --sub_typing                            true
% 38.97/5.50  --prep_gs_sim                           true
% 38.97/5.50  --prep_unflatten                        true
% 38.97/5.50  --prep_res_sim                          true
% 38.97/5.50  --prep_upred                            true
% 38.97/5.50  --prep_sem_filter                       exhaustive
% 38.97/5.50  --prep_sem_filter_out                   false
% 38.97/5.50  --pred_elim                             true
% 38.97/5.50  --res_sim_input                         true
% 38.97/5.50  --eq_ax_congr_red                       true
% 38.97/5.50  --pure_diseq_elim                       true
% 38.97/5.50  --brand_transform                       false
% 38.97/5.50  --non_eq_to_eq                          false
% 38.97/5.50  --prep_def_merge                        true
% 38.97/5.50  --prep_def_merge_prop_impl              false
% 38.97/5.50  --prep_def_merge_mbd                    true
% 38.97/5.50  --prep_def_merge_tr_red                 false
% 38.97/5.50  --prep_def_merge_tr_cl                  false
% 38.97/5.50  --smt_preprocessing                     true
% 38.97/5.50  --smt_ac_axioms                         fast
% 38.97/5.50  --preprocessed_out                      false
% 38.97/5.50  --preprocessed_stats                    false
% 38.97/5.50  
% 38.97/5.50  ------ Abstraction refinement Options
% 38.97/5.50  
% 38.97/5.50  --abstr_ref                             []
% 38.97/5.50  --abstr_ref_prep                        false
% 38.97/5.50  --abstr_ref_until_sat                   false
% 38.97/5.50  --abstr_ref_sig_restrict                funpre
% 38.97/5.50  --abstr_ref_af_restrict_to_split_sk     false
% 38.97/5.50  --abstr_ref_under                       []
% 38.97/5.50  
% 38.97/5.50  ------ SAT Options
% 38.97/5.50  
% 38.97/5.50  --sat_mode                              false
% 38.97/5.50  --sat_fm_restart_options                ""
% 38.97/5.50  --sat_gr_def                            false
% 38.97/5.50  --sat_epr_types                         true
% 38.97/5.50  --sat_non_cyclic_types                  false
% 38.97/5.50  --sat_finite_models                     false
% 38.97/5.50  --sat_fm_lemmas                         false
% 38.97/5.50  --sat_fm_prep                           false
% 38.97/5.50  --sat_fm_uc_incr                        true
% 38.97/5.50  --sat_out_model                         small
% 38.97/5.50  --sat_out_clauses                       false
% 38.97/5.50  
% 38.97/5.50  ------ QBF Options
% 38.97/5.50  
% 38.97/5.50  --qbf_mode                              false
% 38.97/5.50  --qbf_elim_univ                         false
% 38.97/5.50  --qbf_dom_inst                          none
% 38.97/5.50  --qbf_dom_pre_inst                      false
% 38.97/5.50  --qbf_sk_in                             false
% 38.97/5.50  --qbf_pred_elim                         true
% 38.97/5.50  --qbf_split                             512
% 38.97/5.50  
% 38.97/5.50  ------ BMC1 Options
% 38.97/5.50  
% 38.97/5.50  --bmc1_incremental                      false
% 38.97/5.50  --bmc1_axioms                           reachable_all
% 38.97/5.50  --bmc1_min_bound                        0
% 38.97/5.50  --bmc1_max_bound                        -1
% 38.97/5.50  --bmc1_max_bound_default                -1
% 38.97/5.50  --bmc1_symbol_reachability              true
% 38.97/5.50  --bmc1_property_lemmas                  false
% 38.97/5.50  --bmc1_k_induction                      false
% 38.97/5.50  --bmc1_non_equiv_states                 false
% 38.97/5.50  --bmc1_deadlock                         false
% 38.97/5.50  --bmc1_ucm                              false
% 38.97/5.50  --bmc1_add_unsat_core                   none
% 38.97/5.50  --bmc1_unsat_core_children              false
% 38.97/5.50  --bmc1_unsat_core_extrapolate_axioms    false
% 38.97/5.50  --bmc1_out_stat                         full
% 38.97/5.50  --bmc1_ground_init                      false
% 38.97/5.50  --bmc1_pre_inst_next_state              false
% 38.97/5.50  --bmc1_pre_inst_state                   false
% 38.97/5.50  --bmc1_pre_inst_reach_state             false
% 38.97/5.50  --bmc1_out_unsat_core                   false
% 38.97/5.50  --bmc1_aig_witness_out                  false
% 38.97/5.50  --bmc1_verbose                          false
% 38.97/5.50  --bmc1_dump_clauses_tptp                false
% 38.97/5.50  --bmc1_dump_unsat_core_tptp             false
% 38.97/5.50  --bmc1_dump_file                        -
% 38.97/5.50  --bmc1_ucm_expand_uc_limit              128
% 38.97/5.50  --bmc1_ucm_n_expand_iterations          6
% 38.97/5.50  --bmc1_ucm_extend_mode                  1
% 38.97/5.50  --bmc1_ucm_init_mode                    2
% 38.97/5.50  --bmc1_ucm_cone_mode                    none
% 38.97/5.50  --bmc1_ucm_reduced_relation_type        0
% 38.97/5.50  --bmc1_ucm_relax_model                  4
% 38.97/5.50  --bmc1_ucm_full_tr_after_sat            true
% 38.97/5.50  --bmc1_ucm_expand_neg_assumptions       false
% 38.97/5.50  --bmc1_ucm_layered_model                none
% 38.97/5.50  --bmc1_ucm_max_lemma_size               10
% 38.97/5.50  
% 38.97/5.50  ------ AIG Options
% 38.97/5.50  
% 38.97/5.50  --aig_mode                              false
% 38.97/5.50  
% 38.97/5.50  ------ Instantiation Options
% 38.97/5.50  
% 38.97/5.50  --instantiation_flag                    true
% 38.97/5.50  --inst_sos_flag                         true
% 38.97/5.50  --inst_sos_phase                        true
% 38.97/5.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 38.97/5.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 38.97/5.50  --inst_lit_sel_side                     none
% 38.97/5.50  --inst_solver_per_active                1400
% 38.97/5.50  --inst_solver_calls_frac                1.
% 38.97/5.50  --inst_passive_queue_type               priority_queues
% 38.97/5.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 38.97/5.50  --inst_passive_queues_freq              [25;2]
% 38.97/5.50  --inst_dismatching                      true
% 38.97/5.50  --inst_eager_unprocessed_to_passive     true
% 38.97/5.50  --inst_prop_sim_given                   true
% 38.97/5.50  --inst_prop_sim_new                     false
% 38.97/5.50  --inst_subs_new                         false
% 38.97/5.50  --inst_eq_res_simp                      false
% 38.97/5.50  --inst_subs_given                       false
% 38.97/5.50  --inst_orphan_elimination               true
% 38.97/5.50  --inst_learning_loop_flag               true
% 38.97/5.50  --inst_learning_start                   3000
% 38.97/5.50  --inst_learning_factor                  2
% 38.97/5.50  --inst_start_prop_sim_after_learn       3
% 38.97/5.50  --inst_sel_renew                        solver
% 38.97/5.50  --inst_lit_activity_flag                true
% 38.97/5.50  --inst_restr_to_given                   false
% 38.97/5.50  --inst_activity_threshold               500
% 38.97/5.50  --inst_out_proof                        true
% 38.97/5.50  
% 38.97/5.50  ------ Resolution Options
% 38.97/5.50  
% 38.97/5.50  --resolution_flag                       false
% 38.97/5.50  --res_lit_sel                           adaptive
% 38.97/5.50  --res_lit_sel_side                      none
% 38.97/5.50  --res_ordering                          kbo
% 38.97/5.50  --res_to_prop_solver                    active
% 38.97/5.50  --res_prop_simpl_new                    false
% 38.97/5.50  --res_prop_simpl_given                  true
% 38.97/5.50  --res_passive_queue_type                priority_queues
% 38.97/5.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 38.97/5.50  --res_passive_queues_freq               [15;5]
% 38.97/5.50  --res_forward_subs                      full
% 38.97/5.50  --res_backward_subs                     full
% 38.97/5.50  --res_forward_subs_resolution           true
% 38.97/5.50  --res_backward_subs_resolution          true
% 38.97/5.50  --res_orphan_elimination                true
% 38.97/5.50  --res_time_limit                        2.
% 38.97/5.50  --res_out_proof                         true
% 38.97/5.50  
% 38.97/5.50  ------ Superposition Options
% 38.97/5.50  
% 38.97/5.50  --superposition_flag                    true
% 38.97/5.50  --sup_passive_queue_type                priority_queues
% 38.97/5.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 38.97/5.50  --sup_passive_queues_freq               [8;1;4]
% 38.97/5.50  --demod_completeness_check              fast
% 38.97/5.50  --demod_use_ground                      true
% 38.97/5.50  --sup_to_prop_solver                    passive
% 38.97/5.50  --sup_prop_simpl_new                    true
% 38.97/5.50  --sup_prop_simpl_given                  true
% 38.97/5.50  --sup_fun_splitting                     true
% 38.97/5.50  --sup_smt_interval                      50000
% 38.97/5.50  
% 38.97/5.50  ------ Superposition Simplification Setup
% 38.97/5.50  
% 38.97/5.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 38.97/5.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 38.97/5.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 38.97/5.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 38.97/5.50  --sup_full_triv                         [TrivRules;PropSubs]
% 38.97/5.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 38.97/5.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 38.97/5.50  --sup_immed_triv                        [TrivRules]
% 38.97/5.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_immed_bw_main                     []
% 38.97/5.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 38.97/5.50  --sup_input_triv                        [Unflattening;TrivRules]
% 38.97/5.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 38.97/5.50  --sup_input_bw                          []
% 38.97/5.50  
% 38.97/5.50  ------ Combination Options
% 38.97/5.50  
% 38.97/5.50  --comb_res_mult                         3
% 38.97/5.50  --comb_sup_mult                         2
% 38.97/5.50  --comb_inst_mult                        10
% 38.97/5.50  
% 38.97/5.50  ------ Debug Options
% 38.97/5.50  
% 38.97/5.50  --dbg_backtrace                         false
% 38.97/5.50  --dbg_dump_prop_clauses                 false
% 38.97/5.50  --dbg_dump_prop_clauses_file            -
% 38.97/5.50  --dbg_out_stat                          false
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  ------ Proving...
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  % SZS status Theorem for theBenchmark.p
% 38.97/5.50  
% 38.97/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 38.97/5.50  
% 38.97/5.50  fof(f4,axiom,(
% 38.97/5.50    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f63,plain,(
% 38.97/5.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f4])).
% 38.97/5.50  
% 38.97/5.50  fof(f16,axiom,(
% 38.97/5.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f82,plain,(
% 38.97/5.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f16])).
% 38.97/5.50  
% 38.97/5.50  fof(f109,plain,(
% 38.97/5.50    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 38.97/5.50    inference(definition_unfolding,[],[f63,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f2,axiom,(
% 38.97/5.50    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f23,plain,(
% 38.97/5.50    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 38.97/5.50    inference(ennf_transformation,[],[f2])).
% 38.97/5.50  
% 38.97/5.50  fof(f60,plain,(
% 38.97/5.50    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f23])).
% 38.97/5.50  
% 38.97/5.50  fof(f107,plain,(
% 38.97/5.50    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(definition_unfolding,[],[f60,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f1,axiom,(
% 38.97/5.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f59,plain,(
% 38.97/5.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 38.97/5.50    inference(cnf_transformation,[],[f1])).
% 38.97/5.50  
% 38.97/5.50  fof(f105,plain,(
% 38.97/5.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 38.97/5.50    inference(definition_unfolding,[],[f59,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f6,axiom,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f28,plain,(
% 38.97/5.50    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f6])).
% 38.97/5.50  
% 38.97/5.50  fof(f29,plain,(
% 38.97/5.50    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f28])).
% 38.97/5.50  
% 38.97/5.50  fof(f68,plain,(
% 38.97/5.50    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f29])).
% 38.97/5.50  
% 38.97/5.50  fof(f110,plain,(
% 38.97/5.50    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(definition_unfolding,[],[f68,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f58,plain,(
% 38.97/5.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 38.97/5.50    inference(cnf_transformation,[],[f1])).
% 38.97/5.50  
% 38.97/5.50  fof(f106,plain,(
% 38.97/5.50    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 38.97/5.50    inference(definition_unfolding,[],[f58,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f64,plain,(
% 38.97/5.50    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f4])).
% 38.97/5.50  
% 38.97/5.50  fof(f108,plain,(
% 38.97/5.50    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 38.97/5.50    inference(definition_unfolding,[],[f64,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f12,axiom,(
% 38.97/5.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f38,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 38.97/5.50    inference(ennf_transformation,[],[f12])).
% 38.97/5.50  
% 38.97/5.50  fof(f39,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 38.97/5.50    inference(flattening,[],[f38])).
% 38.97/5.50  
% 38.97/5.50  fof(f54,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 38.97/5.50    inference(nnf_transformation,[],[f39])).
% 38.97/5.50  
% 38.97/5.50  fof(f76,plain,(
% 38.97/5.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f54])).
% 38.97/5.50  
% 38.97/5.50  fof(f21,conjecture,(
% 38.97/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f22,negated_conjecture,(
% 38.97/5.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 38.97/5.50    inference(negated_conjecture,[],[f21])).
% 38.97/5.50  
% 38.97/5.50  fof(f52,plain,(
% 38.97/5.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 38.97/5.50    inference(ennf_transformation,[],[f22])).
% 38.97/5.50  
% 38.97/5.50  fof(f53,plain,(
% 38.97/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 38.97/5.50    inference(flattening,[],[f52])).
% 38.97/5.50  
% 38.97/5.50  fof(f56,plain,(
% 38.97/5.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 38.97/5.50    introduced(choice_axiom,[])).
% 38.97/5.50  
% 38.97/5.50  fof(f55,plain,(
% 38.97/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 38.97/5.50    introduced(choice_axiom,[])).
% 38.97/5.50  
% 38.97/5.50  fof(f57,plain,(
% 38.97/5.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 38.97/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f56,f55])).
% 38.97/5.50  
% 38.97/5.50  fof(f100,plain,(
% 38.97/5.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f13,axiom,(
% 38.97/5.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f78,plain,(
% 38.97/5.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f13])).
% 38.97/5.50  
% 38.97/5.50  fof(f114,plain,(
% 38.97/5.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 38.97/5.50    inference(definition_unfolding,[],[f78,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f93,plain,(
% 38.97/5.50    v1_funct_1(sK2)),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f95,plain,(
% 38.97/5.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f96,plain,(
% 38.97/5.50    v1_funct_1(sK3)),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f98,plain,(
% 38.97/5.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f14,axiom,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f40,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 38.97/5.50    inference(ennf_transformation,[],[f14])).
% 38.97/5.50  
% 38.97/5.50  fof(f41,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 38.97/5.50    inference(flattening,[],[f40])).
% 38.97/5.50  
% 38.97/5.50  fof(f80,plain,(
% 38.97/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f41])).
% 38.97/5.50  
% 38.97/5.50  fof(f99,plain,(
% 38.97/5.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f18,axiom,(
% 38.97/5.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f46,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 38.97/5.50    inference(ennf_transformation,[],[f18])).
% 38.97/5.50  
% 38.97/5.50  fof(f47,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 38.97/5.50    inference(flattening,[],[f46])).
% 38.97/5.50  
% 38.97/5.50  fof(f86,plain,(
% 38.97/5.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f47])).
% 38.97/5.50  
% 38.97/5.50  fof(f94,plain,(
% 38.97/5.50    v1_funct_2(sK2,sK0,sK1)),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f97,plain,(
% 38.97/5.50    v1_funct_2(sK3,sK1,sK0)),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f102,plain,(
% 38.97/5.50    k1_xboole_0 != sK0),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  fof(f8,axiom,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f32,plain,(
% 38.97/5.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f8])).
% 38.97/5.50  
% 38.97/5.50  fof(f33,plain,(
% 38.97/5.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f32])).
% 38.97/5.50  
% 38.97/5.50  fof(f71,plain,(
% 38.97/5.50    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f33])).
% 38.97/5.50  
% 38.97/5.50  fof(f112,plain,(
% 38.97/5.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(definition_unfolding,[],[f71,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f10,axiom,(
% 38.97/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f36,plain,(
% 38.97/5.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 38.97/5.50    inference(ennf_transformation,[],[f10])).
% 38.97/5.50  
% 38.97/5.50  fof(f74,plain,(
% 38.97/5.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f36])).
% 38.97/5.50  
% 38.97/5.50  fof(f17,axiom,(
% 38.97/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f44,plain,(
% 38.97/5.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 38.97/5.50    inference(ennf_transformation,[],[f17])).
% 38.97/5.50  
% 38.97/5.50  fof(f45,plain,(
% 38.97/5.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 38.97/5.50    inference(flattening,[],[f44])).
% 38.97/5.50  
% 38.97/5.50  fof(f83,plain,(
% 38.97/5.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f45])).
% 38.97/5.50  
% 38.97/5.50  fof(f20,axiom,(
% 38.97/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f50,plain,(
% 38.97/5.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 38.97/5.50    inference(ennf_transformation,[],[f20])).
% 38.97/5.50  
% 38.97/5.50  fof(f51,plain,(
% 38.97/5.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 38.97/5.50    inference(flattening,[],[f50])).
% 38.97/5.50  
% 38.97/5.50  fof(f91,plain,(
% 38.97/5.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f51])).
% 38.97/5.50  
% 38.97/5.50  fof(f9,axiom,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f34,plain,(
% 38.97/5.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f9])).
% 38.97/5.50  
% 38.97/5.50  fof(f35,plain,(
% 38.97/5.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f34])).
% 38.97/5.50  
% 38.97/5.50  fof(f73,plain,(
% 38.97/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f35])).
% 38.97/5.50  
% 38.97/5.50  fof(f113,plain,(
% 38.97/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(definition_unfolding,[],[f73,f82])).
% 38.97/5.50  
% 38.97/5.50  fof(f11,axiom,(
% 38.97/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f37,plain,(
% 38.97/5.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 38.97/5.50    inference(ennf_transformation,[],[f11])).
% 38.97/5.50  
% 38.97/5.50  fof(f75,plain,(
% 38.97/5.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 38.97/5.50    inference(cnf_transformation,[],[f37])).
% 38.97/5.50  
% 38.97/5.50  fof(f7,axiom,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f30,plain,(
% 38.97/5.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f7])).
% 38.97/5.50  
% 38.97/5.50  fof(f31,plain,(
% 38.97/5.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f30])).
% 38.97/5.50  
% 38.97/5.50  fof(f70,plain,(
% 38.97/5.50    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f31])).
% 38.97/5.50  
% 38.97/5.50  fof(f15,axiom,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f42,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 38.97/5.50    inference(ennf_transformation,[],[f15])).
% 38.97/5.50  
% 38.97/5.50  fof(f43,plain,(
% 38.97/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 38.97/5.50    inference(flattening,[],[f42])).
% 38.97/5.50  
% 38.97/5.50  fof(f81,plain,(
% 38.97/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f43])).
% 38.97/5.50  
% 38.97/5.50  fof(f5,axiom,(
% 38.97/5.50    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f26,plain,(
% 38.97/5.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f5])).
% 38.97/5.50  
% 38.97/5.50  fof(f27,plain,(
% 38.97/5.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f26])).
% 38.97/5.50  
% 38.97/5.50  fof(f67,plain,(
% 38.97/5.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f27])).
% 38.97/5.50  
% 38.97/5.50  fof(f69,plain,(
% 38.97/5.50    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f31])).
% 38.97/5.50  
% 38.97/5.50  fof(f3,axiom,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 38.97/5.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 38.97/5.50  
% 38.97/5.50  fof(f24,plain,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 38.97/5.50    inference(ennf_transformation,[],[f3])).
% 38.97/5.50  
% 38.97/5.50  fof(f25,plain,(
% 38.97/5.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 38.97/5.50    inference(flattening,[],[f24])).
% 38.97/5.50  
% 38.97/5.50  fof(f61,plain,(
% 38.97/5.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f25])).
% 38.97/5.50  
% 38.97/5.50  fof(f62,plain,(
% 38.97/5.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 38.97/5.50    inference(cnf_transformation,[],[f25])).
% 38.97/5.50  
% 38.97/5.50  fof(f104,plain,(
% 38.97/5.50    k2_funct_1(sK2) != sK3),
% 38.97/5.50    inference(cnf_transformation,[],[f57])).
% 38.97/5.50  
% 38.97/5.50  cnf(c_809,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_54494,plain,
% 38.97/5.50      ( k2_funct_1(sK2) != X0 | k2_funct_1(sK2) = sK3 | sK3 != X0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_809]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_91649,plain,
% 38.97/5.50      ( k2_funct_1(sK2) != k2_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | k2_funct_1(sK2) = sK3
% 38.97/5.50      | sK3 != k2_funct_1(k2_funct_1(sK3)) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_54494]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_815,plain,
% 38.97/5.50      ( X0 != X1 | k2_funct_1(X0) = k2_funct_1(X1) ),
% 38.97/5.50      theory(equality) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_65355,plain,
% 38.97/5.50      ( X0 != k2_funct_1(sK3)
% 38.97/5.50      | k2_funct_1(X0) = k2_funct_1(k2_funct_1(sK3)) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_815]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_85173,plain,
% 38.97/5.50      ( k2_funct_1(sK2) = k2_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | sK2 != k2_funct_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_65355]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_55772,plain,
% 38.97/5.50      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_809]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_56962,plain,
% 38.97/5.50      ( X0 != sK2 | sK2 = X0 | sK2 != sK2 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_55772]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_62034,plain,
% 38.97/5.50      ( k2_funct_1(sK3) != sK2 | sK2 = k2_funct_1(sK3) | sK2 != sK2 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_56962]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1589,plain,
% 38.97/5.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_809]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1977,plain,
% 38.97/5.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_1589]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4825,plain,
% 38.97/5.50      ( k2_funct_1(X0) != sK3 | sK3 = k2_funct_1(X0) | sK3 != sK3 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_1977]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_29544,plain,
% 38.97/5.50      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 38.97/5.50      | sK3 = k2_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | sK3 != sK3 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_4825]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6,plain,
% 38.97/5.50      ( v1_relat_1(k6_partfun1(X0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f109]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1430,plain,
% 38.97/5.50      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2,plain,
% 38.97/5.50      ( ~ v1_relat_1(X0)
% 38.97/5.50      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 38.97/5.50      inference(cnf_transformation,[],[f107]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1434,plain,
% 38.97/5.50      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 38.97/5.50      | v1_relat_1(X0) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2628,plain,
% 38.97/5.50      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_1430,c_1434]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_0,plain,
% 38.97/5.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 38.97/5.50      inference(cnf_transformation,[],[f105]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2629,plain,
% 38.97/5.50      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_2628,c_0]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_10,plain,
% 38.97/5.50      ( v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X1)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X1)
% 38.97/5.50      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f110]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1428,plain,
% 38.97/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 38.97/5.50      | v2_funct_1(X0) = iProver_top
% 38.97/5.50      | v1_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_funct_1(X1) != iProver_top
% 38.97/5.50      | v1_relat_1(X0) != iProver_top
% 38.97/5.50      | v1_relat_1(X1) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4419,plain,
% 38.97/5.50      ( k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
% 38.97/5.50      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 38.97/5.50      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 38.97/5.50      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_2629,c_1428]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1,plain,
% 38.97/5.50      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 38.97/5.50      inference(cnf_transformation,[],[f106]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4423,plain,
% 38.97/5.50      ( k6_partfun1(X0) != k6_partfun1(X0)
% 38.97/5.50      | v2_funct_1(k6_partfun1(X0)) = iProver_top
% 38.97/5.50      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 38.97/5.50      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_4419,c_1]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4424,plain,
% 38.97/5.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top
% 38.97/5.50      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 38.97/5.50      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 38.97/5.50      inference(equality_resolution_simp,[status(thm)],[c_4423]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_131,plain,
% 38.97/5.50      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_5,plain,
% 38.97/5.50      ( v1_funct_1(k6_partfun1(X0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f108]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_134,plain,
% 38.97/5.50      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6396,plain,
% 38.97/5.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_4424,c_131,c_134]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_19,plain,
% 38.97/5.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 38.97/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 38.97/5.50      | X3 = X2 ),
% 38.97/5.50      inference(cnf_transformation,[],[f76]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_38,negated_conjecture,
% 38.97/5.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f100]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_493,plain,
% 38.97/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | X3 = X0
% 38.97/5.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 38.97/5.50      | k6_partfun1(sK0) != X3
% 38.97/5.50      | sK0 != X2
% 38.97/5.50      | sK0 != X1 ),
% 38.97/5.50      inference(resolution_lifted,[status(thm)],[c_19,c_38]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_494,plain,
% 38.97/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 38.97/5.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 38.97/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 38.97/5.50      inference(unflattening,[status(thm)],[c_493]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_20,plain,
% 38.97/5.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 38.97/5.50      inference(cnf_transformation,[],[f114]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_502,plain,
% 38.97/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 38.97/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 38.97/5.50      inference(forward_subsumption_resolution,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_494,c_20]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1399,plain,
% 38.97/5.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 38.97/5.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_502]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_45,negated_conjecture,
% 38.97/5.50      ( v1_funct_1(sK2) ),
% 38.97/5.50      inference(cnf_transformation,[],[f93]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_43,negated_conjecture,
% 38.97/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 38.97/5.50      inference(cnf_transformation,[],[f95]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_42,negated_conjecture,
% 38.97/5.50      ( v1_funct_1(sK3) ),
% 38.97/5.50      inference(cnf_transformation,[],[f96]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_40,negated_conjecture,
% 38.97/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 38.97/5.50      inference(cnf_transformation,[],[f98]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_21,plain,
% 38.97/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 38.97/5.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X3) ),
% 38.97/5.50      inference(cnf_transformation,[],[f80]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1526,plain,
% 38.97/5.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 38.97/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 38.97/5.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 38.97/5.50      | ~ v1_funct_1(sK3)
% 38.97/5.50      | ~ v1_funct_1(sK2) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_21]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2442,plain,
% 38.97/5.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_1399,c_45,c_43,c_42,c_40,c_502,c_1526]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_39,negated_conjecture,
% 38.97/5.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 38.97/5.50      inference(cnf_transformation,[],[f99]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_26,plain,
% 38.97/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 38.97/5.50      | ~ v1_funct_2(X3,X4,X1)
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 38.97/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | v2_funct_1(X0)
% 38.97/5.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X3)
% 38.97/5.50      | k2_relset_1(X4,X1,X3) != X1
% 38.97/5.50      | k1_xboole_0 = X2 ),
% 38.97/5.50      inference(cnf_transformation,[],[f86]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1415,plain,
% 38.97/5.50      ( k2_relset_1(X0,X1,X2) != X1
% 38.97/5.50      | k1_xboole_0 = X3
% 38.97/5.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 38.97/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 38.97/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | v2_funct_1(X4) = iProver_top
% 38.97/5.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 38.97/5.50      | v1_funct_1(X4) != iProver_top
% 38.97/5.50      | v1_funct_1(X2) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6311,plain,
% 38.97/5.50      ( k1_xboole_0 = X0
% 38.97/5.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 38.97/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 38.97/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 38.97/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 38.97/5.50      | v2_funct_1(X1) = iProver_top
% 38.97/5.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 38.97/5.50      | v1_funct_1(X1) != iProver_top
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_39,c_1415]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_46,plain,
% 38.97/5.50      ( v1_funct_1(sK2) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_44,negated_conjecture,
% 38.97/5.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 38.97/5.50      inference(cnf_transformation,[],[f94]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_47,plain,
% 38.97/5.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_48,plain,
% 38.97/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6389,plain,
% 38.97/5.50      ( v1_funct_1(X1) != iProver_top
% 38.97/5.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 38.97/5.50      | v2_funct_1(X1) = iProver_top
% 38.97/5.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 38.97/5.50      | k1_xboole_0 = X0
% 38.97/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_6311,c_46,c_47,c_48]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6390,plain,
% 38.97/5.50      ( k1_xboole_0 = X0
% 38.97/5.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 38.97/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 38.97/5.50      | v2_funct_1(X1) = iProver_top
% 38.97/5.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 38.97/5.50      | v1_funct_1(X1) != iProver_top ),
% 38.97/5.50      inference(renaming,[status(thm)],[c_6389]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6393,plain,
% 38.97/5.50      ( sK0 = k1_xboole_0
% 38.97/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 38.97/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 38.97/5.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 38.97/5.50      | v2_funct_1(sK3) = iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_2442,c_6390]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_49,plain,
% 38.97/5.50      ( v1_funct_1(sK3) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_41,negated_conjecture,
% 38.97/5.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f97]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_50,plain,
% 38.97/5.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_51,plain,
% 38.97/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_36,negated_conjecture,
% 38.97/5.50      ( k1_xboole_0 != sK0 ),
% 38.97/5.50      inference(cnf_transformation,[],[f102]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_808,plain,( X0 = X0 ),theory(equality) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_839,plain,
% 38.97/5.50      ( k1_xboole_0 = k1_xboole_0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_808]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1524,plain,
% 38.97/5.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_809]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1525,plain,
% 38.97/5.50      ( sK0 != k1_xboole_0
% 38.97/5.50      | k1_xboole_0 = sK0
% 38.97/5.50      | k1_xboole_0 != k1_xboole_0 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_1524]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6465,plain,
% 38.97/5.50      ( v2_funct_1(sK3) = iProver_top
% 38.97/5.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_6393,c_49,c_50,c_51,c_36,c_839,c_1525]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6466,plain,
% 38.97/5.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 38.97/5.50      | v2_funct_1(sK3) = iProver_top ),
% 38.97/5.50      inference(renaming,[status(thm)],[c_6465]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6469,plain,
% 38.97/5.50      ( v2_funct_1(sK3) = iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_6396,c_6466]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_14,plain,
% 38.97/5.50      ( ~ v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f112]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1424,plain,
% 38.97/5.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 38.97/5.50      | v2_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_relat_1(X0) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6590,plain,
% 38.97/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_6469,c_1424]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_16,plain,
% 38.97/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | v1_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f74]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1578,plain,
% 38.97/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 38.97/5.50      | v1_relat_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_16]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1955,plain,
% 38.97/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 38.97/5.50      | v1_relat_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_1578]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1956,plain,
% 38.97/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_13085,plain,
% 38.97/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_6590,c_49,c_51,c_1956]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_24,plain,
% 38.97/5.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 38.97/5.50      | ~ v1_funct_2(X2,X0,X1)
% 38.97/5.50      | ~ v1_funct_2(X3,X1,X0)
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 38.97/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 38.97/5.50      | ~ v1_funct_1(X2)
% 38.97/5.50      | ~ v1_funct_1(X3)
% 38.97/5.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 38.97/5.50      inference(cnf_transformation,[],[f83]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_506,plain,
% 38.97/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 38.97/5.50      | ~ v1_funct_2(X3,X2,X1)
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 38.97/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X3)
% 38.97/5.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 38.97/5.50      | k2_relset_1(X1,X2,X0) = X2
% 38.97/5.50      | k6_partfun1(X2) != k6_partfun1(sK0)
% 38.97/5.50      | sK0 != X2 ),
% 38.97/5.50      inference(resolution_lifted,[status(thm)],[c_24,c_38]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_507,plain,
% 38.97/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 38.97/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 38.97/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 38.97/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X2)
% 38.97/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 38.97/5.50      | k2_relset_1(X1,sK0,X0) = sK0
% 38.97/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 38.97/5.50      inference(unflattening,[status(thm)],[c_506]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_598,plain,
% 38.97/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 38.97/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 38.97/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 38.97/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X2)
% 38.97/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 38.97/5.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 38.97/5.50      inference(equality_resolution_simp,[status(thm)],[c_507]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1398,plain,
% 38.97/5.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 38.97/5.50      | k2_relset_1(X0,sK0,X2) = sK0
% 38.97/5.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 38.97/5.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 38.97/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 38.97/5.50      | v1_funct_1(X2) != iProver_top
% 38.97/5.50      | v1_funct_1(X1) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_598]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1991,plain,
% 38.97/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 38.97/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 38.97/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 38.97/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 38.97/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top ),
% 38.97/5.50      inference(equality_resolution,[status(thm)],[c_1398]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2449,plain,
% 38.97/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_1991,c_46,c_47,c_48,c_49,c_50,c_51]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_33,plain,
% 38.97/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 38.97/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | ~ v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | k2_relset_1(X1,X2,X0) != X2
% 38.97/5.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 38.97/5.50      | k1_xboole_0 = X2 ),
% 38.97/5.50      inference(cnf_transformation,[],[f91]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1409,plain,
% 38.97/5.50      ( k2_relset_1(X0,X1,X2) != X1
% 38.97/5.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 38.97/5.50      | k1_xboole_0 = X1
% 38.97/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | v2_funct_1(X2) != iProver_top
% 38.97/5.50      | v1_funct_1(X2) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4080,plain,
% 38.97/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 38.97/5.50      | sK0 = k1_xboole_0
% 38.97/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 38.97/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 38.97/5.50      | v2_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_2449,c_1409]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_12941,plain,
% 38.97/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_4080,c_49,c_50,c_51,c_36,c_839,c_1525,c_6469]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_13087,plain,
% 38.97/5.50      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_13085,c_12941]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_13101,plain,
% 38.97/5.50      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_13087,c_0]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_13102,plain,
% 38.97/5.50      ( k1_relat_1(sK3) = sK1 ),
% 38.97/5.50      inference(demodulation,[status(thm)],[c_13101,c_0]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_15,plain,
% 38.97/5.50      ( ~ v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X1)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X1)
% 38.97/5.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 38.97/5.50      | k2_funct_1(X0) = X1
% 38.97/5.50      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 38.97/5.50      inference(cnf_transformation,[],[f113]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1423,plain,
% 38.97/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 38.97/5.50      | k2_funct_1(X1) = X0
% 38.97/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 38.97/5.50      | v2_funct_1(X1) != iProver_top
% 38.97/5.50      | v1_funct_1(X1) != iProver_top
% 38.97/5.50      | v1_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_relat_1(X1) != iProver_top
% 38.97/5.50      | v1_relat_1(X0) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_12943,plain,
% 38.97/5.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 38.97/5.50      | k1_relat_1(k2_funct_1(sK3)) != k2_relat_1(sK3)
% 38.97/5.50      | k6_partfun1(k2_relat_1(k2_funct_1(sK3))) != k6_partfun1(sK1)
% 38.97/5.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_12941,c_1423]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1407,plain,
% 38.97/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_17,plain,
% 38.97/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f75]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1421,plain,
% 38.97/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2737,plain,
% 38.97/5.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_1407,c_1421]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2740,plain,
% 38.97/5.50      ( k2_relat_1(sK3) = sK0 ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_2737,c_2449]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_11,plain,
% 38.97/5.50      ( ~ v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f70]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1427,plain,
% 38.97/5.50      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 38.97/5.50      | v2_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_relat_1(X0) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6591,plain,
% 38.97/5.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_6469,c_1427]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_8061,plain,
% 38.97/5.50      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_6591,c_49,c_51,c_1956]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_12945,plain,
% 38.97/5.50      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 38.97/5.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 38.97/5.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1)
% 38.97/5.50      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(light_normalisation,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_12943,c_2740,c_8061]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_12946,plain,
% 38.97/5.50      ( ~ v2_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v1_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v1_funct_1(sK3)
% 38.97/5.50      | ~ v1_relat_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v1_relat_1(sK3)
% 38.97/5.50      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 38.97/5.50      | k1_relat_1(k2_funct_1(sK3)) != sK0
% 38.97/5.50      | k6_partfun1(k1_relat_1(sK3)) != k6_partfun1(sK1) ),
% 38.97/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_12945]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1404,plain,
% 38.97/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_23,plain,
% 38.97/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 38.97/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X3)
% 38.97/5.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f81]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1417,plain,
% 38.97/5.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 38.97/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 38.97/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | v1_funct_1(X5) != iProver_top
% 38.97/5.50      | v1_funct_1(X4) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4504,plain,
% 38.97/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | v1_funct_1(X2) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_1407,c_1417]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4590,plain,
% 38.97/5.50      ( v1_funct_1(X2) != iProver_top
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_4504,c_49]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4591,plain,
% 38.97/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 38.97/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 38.97/5.50      | v1_funct_1(X2) != iProver_top ),
% 38.97/5.50      inference(renaming,[status(thm)],[c_4590]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4598,plain,
% 38.97/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_1404,c_4591]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4599,plain,
% 38.97/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_4598,c_2442]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_5237,plain,
% 38.97/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_4599,c_46]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_5710,plain,
% 38.97/5.50      ( k2_funct_1(sK3) = sK2
% 38.97/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 38.97/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 38.97/5.50      | v2_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK2) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_5237,c_1423]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2738,plain,
% 38.97/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_1404,c_1421]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2739,plain,
% 38.97/5.50      ( k2_relat_1(sK2) = sK1 ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_2738,c_39]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_5715,plain,
% 38.97/5.50      ( k2_funct_1(sK3) = sK2
% 38.97/5.50      | k1_relat_1(sK3) != sK1
% 38.97/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 38.97/5.50      | v2_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK2) != iProver_top ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_5710,c_2739,c_2740]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_5716,plain,
% 38.97/5.50      ( k2_funct_1(sK3) = sK2
% 38.97/5.50      | k1_relat_1(sK3) != sK1
% 38.97/5.50      | v2_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_funct_1(sK2) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK2) != iProver_top ),
% 38.97/5.50      inference(equality_resolution_simp,[status(thm)],[c_5715]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2350,plain,
% 38.97/5.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 38.97/5.50      | v1_relat_1(sK2) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_16]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2351,plain,
% 38.97/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 38.97/5.50      | v1_relat_1(sK2) = iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_2350]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_11435,plain,
% 38.97/5.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 38.97/5.50      inference(global_propositional_subsumption,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_5716,c_46,c_48,c_49,c_51,c_1956,c_2351,c_6469]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_11436,plain,
% 38.97/5.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 38.97/5.50      inference(renaming,[status(thm)],[c_11435]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_9336,plain,
% 38.97/5.50      ( sK2 = sK2 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_808]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_7,plain,
% 38.97/5.50      ( ~ v2_funct_1(X0)
% 38.97/5.50      | v2_funct_1(k2_funct_1(X0))
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f67]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_8631,plain,
% 38.97/5.50      ( v2_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v2_funct_1(sK3)
% 38.97/5.50      | ~ v1_funct_1(sK3)
% 38.97/5.50      | ~ v1_relat_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_7]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_12,plain,
% 38.97/5.50      ( ~ v2_funct_1(X0)
% 38.97/5.50      | ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f69]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_1426,plain,
% 38.97/5.50      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 38.97/5.50      | v2_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_funct_1(X0) != iProver_top
% 38.97/5.50      | v1_relat_1(X0) != iProver_top ),
% 38.97/5.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6592,plain,
% 38.97/5.50      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(superposition,[status(thm)],[c_6469,c_1426]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6593,plain,
% 38.97/5.50      ( k1_relat_1(k2_funct_1(sK3)) = sK0
% 38.97/5.50      | v1_funct_1(sK3) != iProver_top
% 38.97/5.50      | v1_relat_1(sK3) != iProver_top ),
% 38.97/5.50      inference(light_normalisation,[status(thm)],[c_6592,c_2740]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_6470,plain,
% 38.97/5.50      ( v2_funct_1(sK3) ),
% 38.97/5.50      inference(predicate_to_equality_rev,[status(thm)],[c_6469]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_4,plain,
% 38.97/5.50      ( ~ v1_funct_1(X0)
% 38.97/5.50      | ~ v1_relat_1(X0)
% 38.97/5.50      | v1_relat_1(k2_funct_1(X0)) ),
% 38.97/5.50      inference(cnf_transformation,[],[f61]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_3843,plain,
% 38.97/5.50      ( ~ v1_funct_1(sK3)
% 38.97/5.50      | v1_relat_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v1_relat_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_4]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2645,plain,
% 38.97/5.50      ( sK3 = sK3 ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_808]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_3,plain,
% 38.97/5.50      ( ~ v1_funct_1(X0)
% 38.97/5.50      | v1_funct_1(k2_funct_1(X0))
% 38.97/5.50      | ~ v1_relat_1(X0) ),
% 38.97/5.50      inference(cnf_transformation,[],[f62]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_2331,plain,
% 38.97/5.50      ( v1_funct_1(k2_funct_1(sK3))
% 38.97/5.50      | ~ v1_funct_1(sK3)
% 38.97/5.50      | ~ v1_relat_1(sK3) ),
% 38.97/5.50      inference(instantiation,[status(thm)],[c_3]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(c_34,negated_conjecture,
% 38.97/5.50      ( k2_funct_1(sK2) != sK3 ),
% 38.97/5.50      inference(cnf_transformation,[],[f104]) ).
% 38.97/5.50  
% 38.97/5.50  cnf(contradiction,plain,
% 38.97/5.50      ( $false ),
% 38.97/5.50      inference(minisat,
% 38.97/5.50                [status(thm)],
% 38.97/5.50                [c_91649,c_85173,c_62034,c_29544,c_13102,c_13087,c_12946,
% 38.97/5.50                 c_11436,c_9336,c_8631,c_6593,c_6470,c_3843,c_2645,
% 38.97/5.50                 c_2331,c_1956,c_1955,c_34,c_51,c_40,c_49,c_42]) ).
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 38.97/5.50  
% 38.97/5.50  ------                               Statistics
% 38.97/5.50  
% 38.97/5.50  ------ General
% 38.97/5.50  
% 38.97/5.50  abstr_ref_over_cycles:                  0
% 38.97/5.50  abstr_ref_under_cycles:                 0
% 38.97/5.50  gc_basic_clause_elim:                   0
% 38.97/5.50  forced_gc_time:                         0
% 38.97/5.50  parsing_time:                           0.015
% 38.97/5.50  unif_index_cands_time:                  0.
% 38.97/5.50  unif_index_add_time:                    0.
% 38.97/5.50  orderings_time:                         0.
% 38.97/5.50  out_proof_time:                         0.026
% 38.97/5.50  total_time:                             4.549
% 38.97/5.50  num_of_symbols:                         51
% 38.97/5.50  num_of_terms:                           121762
% 38.97/5.50  
% 38.97/5.50  ------ Preprocessing
% 38.97/5.50  
% 38.97/5.50  num_of_splits:                          0
% 38.97/5.50  num_of_split_atoms:                     0
% 38.97/5.50  num_of_reused_defs:                     0
% 38.97/5.50  num_eq_ax_congr_red:                    0
% 38.97/5.50  num_of_sem_filtered_clauses:            1
% 38.97/5.50  num_of_subtypes:                        0
% 38.97/5.50  monotx_restored_types:                  0
% 38.97/5.50  sat_num_of_epr_types:                   0
% 38.97/5.50  sat_num_of_non_cyclic_types:            0
% 38.97/5.50  sat_guarded_non_collapsed_types:        0
% 38.97/5.50  num_pure_diseq_elim:                    0
% 38.97/5.50  simp_replaced_by:                       0
% 38.97/5.50  res_preprocessed:                       206
% 38.97/5.50  prep_upred:                             0
% 38.97/5.50  prep_unflattend:                        12
% 38.97/5.50  smt_new_axioms:                         0
% 38.97/5.50  pred_elim_cands:                        5
% 38.97/5.50  pred_elim:                              1
% 38.97/5.50  pred_elim_cl:                           1
% 38.97/5.50  pred_elim_cycles:                       3
% 38.97/5.50  merged_defs:                            0
% 38.97/5.50  merged_defs_ncl:                        0
% 38.97/5.50  bin_hyper_res:                          0
% 38.97/5.50  prep_cycles:                            4
% 38.97/5.50  pred_elim_time:                         0.004
% 38.97/5.50  splitting_time:                         0.
% 38.97/5.50  sem_filter_time:                        0.
% 38.97/5.50  monotx_time:                            0.001
% 38.97/5.50  subtype_inf_time:                       0.
% 38.97/5.50  
% 38.97/5.50  ------ Problem properties
% 38.97/5.50  
% 38.97/5.50  clauses:                                43
% 38.97/5.50  conjectures:                            11
% 38.97/5.50  epr:                                    7
% 38.97/5.50  horn:                                   39
% 38.97/5.50  ground:                                 12
% 38.97/5.50  unary:                                  16
% 38.97/5.50  binary:                                 4
% 38.97/5.50  lits:                                   162
% 38.97/5.50  lits_eq:                                36
% 38.97/5.50  fd_pure:                                0
% 38.97/5.50  fd_pseudo:                              0
% 38.97/5.50  fd_cond:                                4
% 38.97/5.50  fd_pseudo_cond:                         1
% 38.97/5.50  ac_symbols:                             0
% 38.97/5.50  
% 38.97/5.50  ------ Propositional Solver
% 38.97/5.50  
% 38.97/5.50  prop_solver_calls:                      50
% 38.97/5.50  prop_fast_solver_calls:                 6247
% 38.97/5.50  smt_solver_calls:                       0
% 38.97/5.50  smt_fast_solver_calls:                  0
% 38.97/5.50  prop_num_of_clauses:                    45076
% 38.97/5.50  prop_preprocess_simplified:             77540
% 38.97/5.50  prop_fo_subsumed:                       1923
% 38.97/5.50  prop_solver_time:                       0.
% 38.97/5.50  smt_solver_time:                        0.
% 38.97/5.50  smt_fast_solver_time:                   0.
% 38.97/5.50  prop_fast_solver_time:                  0.
% 38.97/5.50  prop_unsat_core_time:                   0.008
% 38.97/5.50  
% 38.97/5.50  ------ QBF
% 38.97/5.50  
% 38.97/5.50  qbf_q_res:                              0
% 38.97/5.50  qbf_num_tautologies:                    0
% 38.97/5.50  qbf_prep_cycles:                        0
% 38.97/5.50  
% 38.97/5.50  ------ BMC1
% 38.97/5.50  
% 38.97/5.50  bmc1_current_bound:                     -1
% 38.97/5.50  bmc1_last_solved_bound:                 -1
% 38.97/5.50  bmc1_unsat_core_size:                   -1
% 38.97/5.50  bmc1_unsat_core_parents_size:           -1
% 38.97/5.50  bmc1_merge_next_fun:                    0
% 38.97/5.50  bmc1_unsat_core_clauses_time:           0.
% 38.97/5.50  
% 38.97/5.50  ------ Instantiation
% 38.97/5.50  
% 38.97/5.50  inst_num_of_clauses:                    4628
% 38.97/5.50  inst_num_in_passive:                    2206
% 38.97/5.50  inst_num_in_active:                     4808
% 38.97/5.50  inst_num_in_unprocessed:                340
% 38.97/5.50  inst_num_of_loops:                      5174
% 38.97/5.50  inst_num_of_learning_restarts:          1
% 38.97/5.50  inst_num_moves_active_passive:          361
% 38.97/5.50  inst_lit_activity:                      0
% 38.97/5.50  inst_lit_activity_moves:                8
% 38.97/5.50  inst_num_tautologies:                   0
% 38.97/5.50  inst_num_prop_implied:                  0
% 38.97/5.50  inst_num_existing_simplified:           0
% 38.97/5.50  inst_num_eq_res_simplified:             0
% 38.97/5.50  inst_num_child_elim:                    0
% 38.97/5.50  inst_num_of_dismatching_blockings:      3048
% 38.97/5.50  inst_num_of_non_proper_insts:           9411
% 38.97/5.50  inst_num_of_duplicates:                 0
% 38.97/5.50  inst_inst_num_from_inst_to_res:         0
% 38.97/5.50  inst_dismatching_checking_time:         0.
% 38.97/5.50  
% 38.97/5.50  ------ Resolution
% 38.97/5.50  
% 38.97/5.50  res_num_of_clauses:                     59
% 38.97/5.50  res_num_in_passive:                     59
% 38.97/5.50  res_num_in_active:                      0
% 38.97/5.50  res_num_of_loops:                       210
% 38.97/5.50  res_forward_subset_subsumed:            391
% 38.97/5.50  res_backward_subset_subsumed:           0
% 38.97/5.50  res_forward_subsumed:                   0
% 38.97/5.50  res_backward_subsumed:                  0
% 38.97/5.50  res_forward_subsumption_resolution:     2
% 38.97/5.50  res_backward_subsumption_resolution:    0
% 38.97/5.50  res_clause_to_clause_subsumption:       11432
% 38.97/5.50  res_orphan_elimination:                 0
% 38.97/5.50  res_tautology_del:                      287
% 38.97/5.50  res_num_eq_res_simplified:              1
% 38.97/5.50  res_num_sel_changes:                    0
% 38.97/5.50  res_moves_from_active_to_pass:          0
% 38.97/5.50  
% 38.97/5.50  ------ Superposition
% 38.97/5.50  
% 38.97/5.50  sup_time_total:                         0.
% 38.97/5.50  sup_time_generating:                    0.
% 38.97/5.50  sup_time_sim_full:                      0.
% 38.97/5.50  sup_time_sim_immed:                     0.
% 38.97/5.50  
% 38.97/5.50  sup_num_of_clauses:                     5654
% 38.97/5.50  sup_num_in_active:                      989
% 38.97/5.50  sup_num_in_passive:                     4665
% 38.97/5.50  sup_num_of_loops:                       1034
% 38.97/5.50  sup_fw_superposition:                   2023
% 38.97/5.50  sup_bw_superposition:                   4323
% 38.97/5.50  sup_immediate_simplified:               784
% 38.97/5.50  sup_given_eliminated:                   2
% 38.97/5.50  comparisons_done:                       0
% 38.97/5.50  comparisons_avoided:                    0
% 38.97/5.50  
% 38.97/5.50  ------ Simplifications
% 38.97/5.50  
% 38.97/5.50  
% 38.97/5.50  sim_fw_subset_subsumed:                 109
% 38.97/5.50  sim_bw_subset_subsumed:                 115
% 38.97/5.50  sim_fw_subsumed:                        50
% 38.97/5.50  sim_bw_subsumed:                        5
% 38.97/5.50  sim_fw_subsumption_res:                 0
% 38.97/5.50  sim_bw_subsumption_res:                 0
% 38.97/5.50  sim_tautology_del:                      117
% 38.97/5.50  sim_eq_tautology_del:                   201
% 38.97/5.50  sim_eq_res_simp:                        18
% 38.97/5.50  sim_fw_demodulated:                     199
% 38.97/5.50  sim_bw_demodulated:                     21
% 38.97/5.50  sim_light_normalised:                   609
% 38.97/5.50  sim_joinable_taut:                      0
% 38.97/5.50  sim_joinable_simp:                      0
% 38.97/5.50  sim_ac_normalised:                      0
% 38.97/5.50  sim_smt_subsumption:                    0
% 38.97/5.50  
%------------------------------------------------------------------------------
