%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:08 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.60s
% Verified   : 
% Statistics : Number of formulae       :  202 (1231 expanded)
%              Number of clauses        :  132 ( 330 expanded)
%              Number of leaves         :   17 ( 330 expanded)
%              Depth                    :   23
%              Number of atoms          :  825 (10981 expanded)
%              Number of equality atoms :  417 (3996 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f39,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f27])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f21])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f71,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f16,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f42,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f79,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f74,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f43,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f1,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f58])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f58])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1220,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1223,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1224,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3952,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1224])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4369,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3952,c_38])).

cnf(c_4370,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4369])).

cnf(c_4380,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_4370])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1602,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1602])).

cnf(c_2346,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1894])).

cnf(c_3680,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_4615,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4380,c_34,c_32,c_31,c_29,c_3680])).

cnf(c_8,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_334,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_27])).

cnf(c_335,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_1217,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_335])).

cnf(c_4618,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4615,c_1217])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_405,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_406,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_410,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_34])).

cnf(c_411,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_410])).

cnf(c_1467,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_411])).

cnf(c_1468,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1467])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_453,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_454,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_458,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_34])).

cnf(c_459,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_458])).

cnf(c_1493,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_459])).

cnf(c_1494,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1493])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4620,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4615,c_1226])).

cnf(c_1212,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_2024,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_1212])).

cnf(c_2275,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2024,c_36,c_37,c_28,c_1494])).

cnf(c_3954,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2275,c_1224])).

cnf(c_4868,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3954,c_36,c_37,c_28,c_1468])).

cnf(c_4869,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4868])).

cnf(c_4879,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_4869])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_351,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_352,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_356,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_352,c_34])).

cnf(c_357,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_1216,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_507,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_26])).

cnf(c_508,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_510,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_508,c_34])).

cnf(c_1210,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_510])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1507,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1751,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1210,c_34,c_32,c_508,c_1507])).

cnf(c_3102,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1216,c_1751])).

cnf(c_3109,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_3102])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_753,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_784,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_753])).

cnf(c_754,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1532,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1533,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1532])).

cnf(c_3716,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3109,c_36,c_37,c_24,c_784,c_1533])).

cnf(c_3720,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_3716,c_1751])).

cnf(c_4887,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4879,c_3720])).

cnf(c_5327,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4887,c_35])).

cnf(c_5330,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5327,c_1226])).

cnf(c_7739,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4618,c_35,c_36,c_37,c_38,c_40,c_28,c_1468,c_1494,c_4620,c_5330])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_378,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_379,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_383,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_379,c_34])).

cnf(c_384,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_383])).

cnf(c_1215,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_521,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_26])).

cnf(c_522,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_521])).

cnf(c_524,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_34])).

cnf(c_1209,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_524])).

cnf(c_1633,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1209,c_34,c_32,c_522,c_1507])).

cnf(c_2327,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_1633])).

cnf(c_2334,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_28,c_2327])).

cnf(c_2608,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2334,c_36,c_37,c_24,c_784,c_1533])).

cnf(c_0,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2627,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2608,c_0])).

cnf(c_2629,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_2627,c_0])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_477,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_26])).

cnf(c_478,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_482,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_34])).

cnf(c_483,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2) ),
    inference(renaming,[status(thm)],[c_482])).

cnf(c_1211,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_484,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_483])).

cnf(c_1508,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_2313,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1211,c_37,c_484,c_1508])).

cnf(c_2314,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2313])).

cnf(c_3112,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2629,c_2314])).

cnf(c_3735,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3716,c_0])).

cnf(c_3737,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_3735,c_0])).

cnf(c_4176,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3112,c_3737])).

cnf(c_7743,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK3) != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7739,c_4176])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1227,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3688,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1227])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1233,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2449,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1223,c_1233])).

cnf(c_3708,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3688,c_2449])).

cnf(c_1534,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_1535,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1534])).

cnf(c_1504,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1505,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1504])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7743,c_3708,c_1535,c_1505,c_784,c_23,c_25,c_40,c_39,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.60/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.60/0.99  
% 3.60/0.99  ------  iProver source info
% 3.60/0.99  
% 3.60/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.60/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.60/0.99  git: non_committed_changes: false
% 3.60/0.99  git: last_make_outside_of_git: false
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    --mode clausify
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         false
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     num_symb
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       true
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     false
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   []
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_full_bw                           [BwDemod]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  ------ Parsing...
% 3.60/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.60/0.99  ------ Proving...
% 3.60/0.99  ------ Problem Properties 
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  clauses                                 32
% 3.60/0.99  conjectures                             10
% 3.60/0.99  EPR                                     6
% 3.60/0.99  Horn                                    26
% 3.60/0.99  unary                                   12
% 3.60/0.99  binary                                  4
% 3.60/0.99  lits                                    87
% 3.60/0.99  lits eq                                 32
% 3.60/0.99  fd_pure                                 0
% 3.60/0.99  fd_pseudo                               0
% 3.60/0.99  fd_cond                                 6
% 3.60/0.99  fd_pseudo_cond                          0
% 3.60/0.99  AC symbols                              0
% 3.60/0.99  
% 3.60/0.99  ------ Schedule dynamic 5 is on 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ 
% 3.60/0.99  Current options:
% 3.60/0.99  ------ 
% 3.60/0.99  
% 3.60/0.99  ------ Input Options
% 3.60/0.99  
% 3.60/0.99  --out_options                           all
% 3.60/0.99  --tptp_safe_out                         true
% 3.60/0.99  --problem_path                          ""
% 3.60/0.99  --include_path                          ""
% 3.60/0.99  --clausifier                            res/vclausify_rel
% 3.60/0.99  --clausifier_options                    --mode clausify
% 3.60/0.99  --stdin                                 false
% 3.60/0.99  --stats_out                             all
% 3.60/0.99  
% 3.60/0.99  ------ General Options
% 3.60/0.99  
% 3.60/0.99  --fof                                   false
% 3.60/0.99  --time_out_real                         305.
% 3.60/0.99  --time_out_virtual                      -1.
% 3.60/0.99  --symbol_type_check                     false
% 3.60/0.99  --clausify_out                          false
% 3.60/0.99  --sig_cnt_out                           false
% 3.60/0.99  --trig_cnt_out                          false
% 3.60/0.99  --trig_cnt_out_tolerance                1.
% 3.60/0.99  --trig_cnt_out_sk_spl                   false
% 3.60/0.99  --abstr_cl_out                          false
% 3.60/0.99  
% 3.60/0.99  ------ Global Options
% 3.60/0.99  
% 3.60/0.99  --schedule                              default
% 3.60/0.99  --add_important_lit                     false
% 3.60/0.99  --prop_solver_per_cl                    1000
% 3.60/0.99  --min_unsat_core                        false
% 3.60/0.99  --soft_assumptions                      false
% 3.60/0.99  --soft_lemma_size                       3
% 3.60/0.99  --prop_impl_unit_size                   0
% 3.60/0.99  --prop_impl_unit                        []
% 3.60/0.99  --share_sel_clauses                     true
% 3.60/0.99  --reset_solvers                         false
% 3.60/0.99  --bc_imp_inh                            [conj_cone]
% 3.60/0.99  --conj_cone_tolerance                   3.
% 3.60/0.99  --extra_neg_conj                        none
% 3.60/0.99  --large_theory_mode                     true
% 3.60/0.99  --prolific_symb_bound                   200
% 3.60/0.99  --lt_threshold                          2000
% 3.60/0.99  --clause_weak_htbl                      true
% 3.60/0.99  --gc_record_bc_elim                     false
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing Options
% 3.60/0.99  
% 3.60/0.99  --preprocessing_flag                    true
% 3.60/0.99  --time_out_prep_mult                    0.1
% 3.60/0.99  --splitting_mode                        input
% 3.60/0.99  --splitting_grd                         true
% 3.60/0.99  --splitting_cvd                         false
% 3.60/0.99  --splitting_cvd_svl                     false
% 3.60/0.99  --splitting_nvd                         32
% 3.60/0.99  --sub_typing                            true
% 3.60/0.99  --prep_gs_sim                           true
% 3.60/0.99  --prep_unflatten                        true
% 3.60/0.99  --prep_res_sim                          true
% 3.60/0.99  --prep_upred                            true
% 3.60/0.99  --prep_sem_filter                       exhaustive
% 3.60/0.99  --prep_sem_filter_out                   false
% 3.60/0.99  --pred_elim                             true
% 3.60/0.99  --res_sim_input                         true
% 3.60/0.99  --eq_ax_congr_red                       true
% 3.60/0.99  --pure_diseq_elim                       true
% 3.60/0.99  --brand_transform                       false
% 3.60/0.99  --non_eq_to_eq                          false
% 3.60/0.99  --prep_def_merge                        true
% 3.60/0.99  --prep_def_merge_prop_impl              false
% 3.60/0.99  --prep_def_merge_mbd                    true
% 3.60/0.99  --prep_def_merge_tr_red                 false
% 3.60/0.99  --prep_def_merge_tr_cl                  false
% 3.60/0.99  --smt_preprocessing                     true
% 3.60/0.99  --smt_ac_axioms                         fast
% 3.60/0.99  --preprocessed_out                      false
% 3.60/0.99  --preprocessed_stats                    false
% 3.60/0.99  
% 3.60/0.99  ------ Abstraction refinement Options
% 3.60/0.99  
% 3.60/0.99  --abstr_ref                             []
% 3.60/0.99  --abstr_ref_prep                        false
% 3.60/0.99  --abstr_ref_until_sat                   false
% 3.60/0.99  --abstr_ref_sig_restrict                funpre
% 3.60/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.60/0.99  --abstr_ref_under                       []
% 3.60/0.99  
% 3.60/0.99  ------ SAT Options
% 3.60/0.99  
% 3.60/0.99  --sat_mode                              false
% 3.60/0.99  --sat_fm_restart_options                ""
% 3.60/0.99  --sat_gr_def                            false
% 3.60/0.99  --sat_epr_types                         true
% 3.60/0.99  --sat_non_cyclic_types                  false
% 3.60/0.99  --sat_finite_models                     false
% 3.60/0.99  --sat_fm_lemmas                         false
% 3.60/0.99  --sat_fm_prep                           false
% 3.60/0.99  --sat_fm_uc_incr                        true
% 3.60/0.99  --sat_out_model                         small
% 3.60/0.99  --sat_out_clauses                       false
% 3.60/0.99  
% 3.60/0.99  ------ QBF Options
% 3.60/0.99  
% 3.60/0.99  --qbf_mode                              false
% 3.60/0.99  --qbf_elim_univ                         false
% 3.60/0.99  --qbf_dom_inst                          none
% 3.60/0.99  --qbf_dom_pre_inst                      false
% 3.60/0.99  --qbf_sk_in                             false
% 3.60/0.99  --qbf_pred_elim                         true
% 3.60/0.99  --qbf_split                             512
% 3.60/0.99  
% 3.60/0.99  ------ BMC1 Options
% 3.60/0.99  
% 3.60/0.99  --bmc1_incremental                      false
% 3.60/0.99  --bmc1_axioms                           reachable_all
% 3.60/0.99  --bmc1_min_bound                        0
% 3.60/0.99  --bmc1_max_bound                        -1
% 3.60/0.99  --bmc1_max_bound_default                -1
% 3.60/0.99  --bmc1_symbol_reachability              true
% 3.60/0.99  --bmc1_property_lemmas                  false
% 3.60/0.99  --bmc1_k_induction                      false
% 3.60/0.99  --bmc1_non_equiv_states                 false
% 3.60/0.99  --bmc1_deadlock                         false
% 3.60/0.99  --bmc1_ucm                              false
% 3.60/0.99  --bmc1_add_unsat_core                   none
% 3.60/0.99  --bmc1_unsat_core_children              false
% 3.60/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.60/0.99  --bmc1_out_stat                         full
% 3.60/0.99  --bmc1_ground_init                      false
% 3.60/0.99  --bmc1_pre_inst_next_state              false
% 3.60/0.99  --bmc1_pre_inst_state                   false
% 3.60/0.99  --bmc1_pre_inst_reach_state             false
% 3.60/0.99  --bmc1_out_unsat_core                   false
% 3.60/0.99  --bmc1_aig_witness_out                  false
% 3.60/0.99  --bmc1_verbose                          false
% 3.60/0.99  --bmc1_dump_clauses_tptp                false
% 3.60/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.60/0.99  --bmc1_dump_file                        -
% 3.60/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.60/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.60/0.99  --bmc1_ucm_extend_mode                  1
% 3.60/0.99  --bmc1_ucm_init_mode                    2
% 3.60/0.99  --bmc1_ucm_cone_mode                    none
% 3.60/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.60/0.99  --bmc1_ucm_relax_model                  4
% 3.60/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.60/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.60/0.99  --bmc1_ucm_layered_model                none
% 3.60/0.99  --bmc1_ucm_max_lemma_size               10
% 3.60/0.99  
% 3.60/0.99  ------ AIG Options
% 3.60/0.99  
% 3.60/0.99  --aig_mode                              false
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation Options
% 3.60/0.99  
% 3.60/0.99  --instantiation_flag                    true
% 3.60/0.99  --inst_sos_flag                         false
% 3.60/0.99  --inst_sos_phase                        true
% 3.60/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.60/0.99  --inst_lit_sel_side                     none
% 3.60/0.99  --inst_solver_per_active                1400
% 3.60/0.99  --inst_solver_calls_frac                1.
% 3.60/0.99  --inst_passive_queue_type               priority_queues
% 3.60/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.60/0.99  --inst_passive_queues_freq              [25;2]
% 3.60/0.99  --inst_dismatching                      true
% 3.60/0.99  --inst_eager_unprocessed_to_passive     true
% 3.60/0.99  --inst_prop_sim_given                   true
% 3.60/0.99  --inst_prop_sim_new                     false
% 3.60/0.99  --inst_subs_new                         false
% 3.60/0.99  --inst_eq_res_simp                      false
% 3.60/0.99  --inst_subs_given                       false
% 3.60/0.99  --inst_orphan_elimination               true
% 3.60/0.99  --inst_learning_loop_flag               true
% 3.60/0.99  --inst_learning_start                   3000
% 3.60/0.99  --inst_learning_factor                  2
% 3.60/0.99  --inst_start_prop_sim_after_learn       3
% 3.60/0.99  --inst_sel_renew                        solver
% 3.60/0.99  --inst_lit_activity_flag                true
% 3.60/0.99  --inst_restr_to_given                   false
% 3.60/0.99  --inst_activity_threshold               500
% 3.60/0.99  --inst_out_proof                        true
% 3.60/0.99  
% 3.60/0.99  ------ Resolution Options
% 3.60/0.99  
% 3.60/0.99  --resolution_flag                       false
% 3.60/0.99  --res_lit_sel                           adaptive
% 3.60/0.99  --res_lit_sel_side                      none
% 3.60/0.99  --res_ordering                          kbo
% 3.60/0.99  --res_to_prop_solver                    active
% 3.60/0.99  --res_prop_simpl_new                    false
% 3.60/0.99  --res_prop_simpl_given                  true
% 3.60/0.99  --res_passive_queue_type                priority_queues
% 3.60/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.60/0.99  --res_passive_queues_freq               [15;5]
% 3.60/0.99  --res_forward_subs                      full
% 3.60/0.99  --res_backward_subs                     full
% 3.60/0.99  --res_forward_subs_resolution           true
% 3.60/0.99  --res_backward_subs_resolution          true
% 3.60/0.99  --res_orphan_elimination                true
% 3.60/0.99  --res_time_limit                        2.
% 3.60/0.99  --res_out_proof                         true
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Options
% 3.60/0.99  
% 3.60/0.99  --superposition_flag                    true
% 3.60/0.99  --sup_passive_queue_type                priority_queues
% 3.60/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.60/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.60/0.99  --demod_completeness_check              fast
% 3.60/0.99  --demod_use_ground                      true
% 3.60/0.99  --sup_to_prop_solver                    passive
% 3.60/0.99  --sup_prop_simpl_new                    true
% 3.60/0.99  --sup_prop_simpl_given                  true
% 3.60/0.99  --sup_fun_splitting                     false
% 3.60/0.99  --sup_smt_interval                      50000
% 3.60/0.99  
% 3.60/0.99  ------ Superposition Simplification Setup
% 3.60/0.99  
% 3.60/0.99  --sup_indices_passive                   []
% 3.60/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.60/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.60/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_full_bw                           [BwDemod]
% 3.60/0.99  --sup_immed_triv                        [TrivRules]
% 3.60/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.60/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_immed_bw_main                     []
% 3.60/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.60/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.60/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.60/0.99  
% 3.60/0.99  ------ Combination Options
% 3.60/0.99  
% 3.60/0.99  --comb_res_mult                         3
% 3.60/0.99  --comb_sup_mult                         2
% 3.60/0.99  --comb_inst_mult                        10
% 3.60/0.99  
% 3.60/0.99  ------ Debug Options
% 3.60/0.99  
% 3.60/0.99  --dbg_backtrace                         false
% 3.60/0.99  --dbg_dump_prop_clauses                 false
% 3.60/0.99  --dbg_dump_prop_clauses_file            -
% 3.60/0.99  --dbg_out_stat                          false
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  ------ Proving...
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS status Theorem for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  fof(f13,conjecture,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f14,negated_conjecture,(
% 3.60/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.60/0.99    inference(negated_conjecture,[],[f13])).
% 3.60/0.99  
% 3.60/0.99  fof(f33,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f14])).
% 3.60/0.99  
% 3.60/0.99  fof(f34,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f33])).
% 3.60/0.99  
% 3.60/0.99  fof(f38,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f37,plain,(
% 3.60/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.60/0.99    introduced(choice_axiom,[])).
% 3.60/0.99  
% 3.60/0.99  fof(f39,plain,(
% 3.60/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.60/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).
% 3.60/0.99  
% 3.60/0.99  fof(f66,plain,(
% 3.60/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f69,plain,(
% 3.60/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f9,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f27,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/0.99    inference(ennf_transformation,[],[f9])).
% 3.60/0.99  
% 3.60/0.99  fof(f28,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/0.99    inference(flattening,[],[f27])).
% 3.60/0.99  
% 3.60/0.99  fof(f57,plain,(
% 3.60/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f28])).
% 3.60/0.99  
% 3.60/0.99  fof(f67,plain,(
% 3.60/0.99    v1_funct_1(sK3)),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f64,plain,(
% 3.60/0.99    v1_funct_1(sK2)),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f6,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f21,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.60/0.99    inference(ennf_transformation,[],[f6])).
% 3.60/0.99  
% 3.60/0.99  fof(f22,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(flattening,[],[f21])).
% 3.60/0.99  
% 3.60/0.99  fof(f35,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f22])).
% 3.60/0.99  
% 3.60/0.99  fof(f47,plain,(
% 3.60/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f35])).
% 3.60/0.99  
% 3.60/0.99  fof(f71,plain,(
% 3.60/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f65,plain,(
% 3.60/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f70,plain,(
% 3.60/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f11,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f29,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f11])).
% 3.60/0.99  
% 3.60/0.99  fof(f30,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f29])).
% 3.60/0.99  
% 3.60/0.99  fof(f59,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f30])).
% 3.60/0.99  
% 3.60/0.99  fof(f72,plain,(
% 3.60/0.99    v2_funct_1(sK2)),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f61,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f30])).
% 3.60/0.99  
% 3.60/0.99  fof(f8,axiom,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f25,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.60/0.99    inference(ennf_transformation,[],[f8])).
% 3.60/0.99  
% 3.60/0.99  fof(f26,plain,(
% 3.60/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.60/0.99    inference(flattening,[],[f25])).
% 3.60/0.99  
% 3.60/0.99  fof(f56,plain,(
% 3.60/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f26])).
% 3.60/0.99  
% 3.60/0.99  fof(f12,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f31,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.60/0.99    inference(ennf_transformation,[],[f12])).
% 3.60/0.99  
% 3.60/0.99  fof(f32,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.60/0.99    inference(flattening,[],[f31])).
% 3.60/0.99  
% 3.60/0.99  fof(f62,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f32])).
% 3.60/0.99  
% 3.60/0.99  fof(f2,axiom,(
% 3.60/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f15,plain,(
% 3.60/0.99    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.60/0.99    inference(ennf_transformation,[],[f2])).
% 3.60/0.99  
% 3.60/0.99  fof(f16,plain,(
% 3.60/0.99    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.60/0.99    inference(flattening,[],[f15])).
% 3.60/0.99  
% 3.60/0.99  fof(f42,plain,(
% 3.60/0.99    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f16])).
% 3.60/0.99  
% 3.60/0.99  fof(f10,axiom,(
% 3.60/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f58,plain,(
% 3.60/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f10])).
% 3.60/0.99  
% 3.60/0.99  fof(f79,plain,(
% 3.60/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f42,f58])).
% 3.60/0.99  
% 3.60/0.99  fof(f4,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f19,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f4])).
% 3.60/0.99  
% 3.60/0.99  fof(f45,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f19])).
% 3.60/0.99  
% 3.60/0.99  fof(f74,plain,(
% 3.60/0.99    k1_xboole_0 != sK1),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f63,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f32])).
% 3.60/0.99  
% 3.60/0.99  fof(f43,plain,(
% 3.60/0.99    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f16])).
% 3.60/0.99  
% 3.60/0.99  fof(f78,plain,(
% 3.60/0.99    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f43,f58])).
% 3.60/0.99  
% 3.60/0.99  fof(f1,axiom,(
% 3.60/0.99    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f41,plain,(
% 3.60/0.99    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.60/0.99    inference(cnf_transformation,[],[f1])).
% 3.60/0.99  
% 3.60/0.99  fof(f76,plain,(
% 3.60/0.99    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.60/0.99    inference(definition_unfolding,[],[f41,f58])).
% 3.60/0.99  
% 3.60/0.99  fof(f3,axiom,(
% 3.60/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f17,plain,(
% 3.60/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.60/0.99    inference(ennf_transformation,[],[f3])).
% 3.60/0.99  
% 3.60/0.99  fof(f18,plain,(
% 3.60/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.60/0.99    inference(flattening,[],[f17])).
% 3.60/0.99  
% 3.60/0.99  fof(f44,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(cnf_transformation,[],[f18])).
% 3.60/0.99  
% 3.60/0.99  fof(f80,plain,(
% 3.60/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.60/0.99    inference(definition_unfolding,[],[f44,f58])).
% 3.60/0.99  
% 3.60/0.99  fof(f7,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f23,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f7])).
% 3.60/0.99  
% 3.60/0.99  fof(f24,plain,(
% 3.60/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(flattening,[],[f23])).
% 3.60/0.99  
% 3.60/0.99  fof(f36,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(nnf_transformation,[],[f24])).
% 3.60/0.99  
% 3.60/0.99  fof(f49,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f36])).
% 3.60/0.99  
% 3.60/0.99  fof(f5,axiom,(
% 3.60/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.60/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.60/0.99  
% 3.60/0.99  fof(f20,plain,(
% 3.60/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.60/0.99    inference(ennf_transformation,[],[f5])).
% 3.60/0.99  
% 3.60/0.99  fof(f46,plain,(
% 3.60/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.60/0.99    inference(cnf_transformation,[],[f20])).
% 3.60/0.99  
% 3.60/0.99  fof(f75,plain,(
% 3.60/0.99    k2_funct_1(sK2) != sK3),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f73,plain,(
% 3.60/0.99    k1_xboole_0 != sK0),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  fof(f68,plain,(
% 3.60/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.60/0.99    inference(cnf_transformation,[],[f39])).
% 3.60/0.99  
% 3.60/0.99  cnf(c_32,negated_conjecture,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1220,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_29,negated_conjecture,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.60/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1223,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_17,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X3)
% 3.60/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1224,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.60/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.60/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X5) != iProver_top
% 3.60/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3952,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1223,c_1224]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_31,negated_conjecture,
% 3.60/0.99      ( v1_funct_1(sK3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_38,plain,
% 3.60/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4369,plain,
% 3.60/0.99      ( v1_funct_1(X2) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3952,c_38]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4370,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_4369]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4380,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_4370]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_34,negated_conjecture,
% 3.60/0.99      ( v1_funct_1(sK2) ),
% 3.60/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1602,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1894,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1602]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2346,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1894]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3680,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | ~ v1_funct_1(sK3)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_2346]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4615,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4380,c_34,c_32,c_31,c_29,c_3680]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_8,plain,
% 3.60/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.60/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | X3 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_27,negated_conjecture,
% 3.60/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_334,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | X3 = X0
% 3.60/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.60/0.99      | k6_partfun1(sK0) != X3
% 3.60/0.99      | sK0 != X2
% 3.60/0.99      | sK0 != X1 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_27]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_335,plain,
% 3.60/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.60/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_334]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1217,plain,
% 3.60/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.60/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_335]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4618,plain,
% 3.60/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.60/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_4615,c_1217]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_35,plain,
% 3.60/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_33,negated_conjecture,
% 3.60/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.60/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_36,plain,
% 3.60/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_37,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_40,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_28,negated_conjecture,
% 3.60/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_20,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_26,negated_conjecture,
% 3.60/0.99      ( v2_funct_1(sK2) ),
% 3.60/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_405,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | sK2 != X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_406,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_405]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_410,plain,
% 3.60/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_406,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_411,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_410]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1467,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.60/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_411]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1468,plain,
% 3.60/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1467]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_18,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_453,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | sK2 != X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_454,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_453]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_458,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.60/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_454,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_459,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_458]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1493,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_459]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1494,plain,
% 3.60/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1493]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_15,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.60/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X3) ),
% 3.60/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1226,plain,
% 3.60/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.60/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.60/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top
% 3.60/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4620,plain,
% 3.60/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_4615,c_1226]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1212,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2024,plain,
% 3.60/0.99      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_28,c_1212]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2275,plain,
% 3.60/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_2024,c_36,c_37,c_28,c_1494]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3954,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_2275,c_1224]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4868,plain,
% 3.60/0.99      ( v1_funct_1(X2) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3954,c_36,c_37,c_28,c_1468]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4869,plain,
% 3.60/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.60/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_4868]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4879,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1220,c_4869]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_22,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_351,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.60/0.99      | sK2 != X0
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_352,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_356,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_352,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_357,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_356]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1216,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_507,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 3.60/0.99      | sK2 != X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_3,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_508,plain,
% 3.60/0.99      ( ~ v1_relat_1(sK2)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_507]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_510,plain,
% 3.60/0.99      ( ~ v1_relat_1(sK2)
% 3.60/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_508,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1210,plain,
% 3.60/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_510]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | v1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1507,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.60/0.99      | v1_relat_1(sK2) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1751,plain,
% 3.60/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1210,c_34,c_32,c_508,c_1507]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3102,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(X0)
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_1216,c_1751]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3109,plain,
% 3.60/0.99      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0)
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_28,c_3102]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_24,negated_conjecture,
% 3.60/0.99      ( k1_xboole_0 != sK1 ),
% 3.60/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_753,plain,( X0 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_784,plain,
% 3.60/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_753]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_754,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1532,plain,
% 3.60/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_754]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1533,plain,
% 3.60/0.99      ( sK1 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK1
% 3.60/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1532]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3716,plain,
% 3.60/0.99      ( k6_partfun1(k1_relat_1(sK2)) = k6_partfun1(sK0) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_3109,c_36,c_37,c_24,c_784,c_1533]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3720,plain,
% 3.60/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3716,c_1751]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4887,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_4879,c_3720]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5327,plain,
% 3.60/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4887,c_35]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_5330,plain,
% 3.60/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.60/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_5327,c_1226]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7739,plain,
% 3.60/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_4618,c_35,c_36,c_37,c_38,c_40,c_28,c_1468,c_1494,
% 3.60/0.99                 c_4620,c_5330]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_21,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_378,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.60/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.60/0.99      | sK2 != X0
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_379,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_378]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_383,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_379,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_384,plain,
% 3.60/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.60/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.60/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X1 ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_383]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1215,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 3.60/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_521,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 3.60/0.99      | sK2 != X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_522,plain,
% 3.60/0.99      ( ~ v1_relat_1(sK2)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_521]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_524,plain,
% 3.60/0.99      ( ~ v1_relat_1(sK2)
% 3.60/0.99      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_522,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1209,plain,
% 3.60/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_524]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1633,plain,
% 3.60/0.99      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1209,c_34,c_32,c_522,c_1507]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2327,plain,
% 3.60/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.60/0.99      | k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(X1)
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_1215,c_1633]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2334,plain,
% 3.60/0.99      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1)
% 3.60/0.99      | sK1 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.60/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_28,c_2327]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2608,plain,
% 3.60/0.99      ( k6_partfun1(k2_relat_1(sK2)) = k6_partfun1(sK1) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_2334,c_36,c_37,c_24,c_784,c_1533]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_0,plain,
% 3.60/0.99      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2627,plain,
% 3.60/0.99      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_2608,c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2629,plain,
% 3.60/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_2627,c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X1)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X1)
% 3.60/0.99      | ~ v2_funct_1(X0)
% 3.60/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.60/0.99      | k2_funct_1(X0) = X1
% 3.60/0.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_477,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_relat_1(X1)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(X1)
% 3.60/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.60/0.99      | k2_funct_1(X0) = X1
% 3.60/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.60/0.99      | sK2 != X0 ),
% 3.60/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_26]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_478,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_relat_1(sK2)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_funct_1(sK2)
% 3.60/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2) ),
% 3.60/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_482,plain,
% 3.60/0.99      ( ~ v1_funct_1(X0)
% 3.60/0.99      | ~ v1_relat_1(sK2)
% 3.60/0.99      | ~ v1_relat_1(X0)
% 3.60/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2) ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_478,c_34]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_483,plain,
% 3.60/0.99      ( ~ v1_relat_1(X0)
% 3.60/0.99      | ~ v1_relat_1(sK2)
% 3.60/0.99      | ~ v1_funct_1(X0)
% 3.60/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2) ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_482]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1211,plain,
% 3.60/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_484,plain,
% 3.60/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_483]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1508,plain,
% 3.60/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.60/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2313,plain,
% 3.60/0.99      ( v1_relat_1(X0) != iProver_top
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(global_propositional_subsumption,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_1211,c_37,c_484,c_1508]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2314,plain,
% 3.60/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(renaming,[status(thm)],[c_2313]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3112,plain,
% 3.60/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != sK1
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_2629,c_2314]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3735,plain,
% 3.60/0.99      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_3716,c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3737,plain,
% 3.60/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3735,c_0]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_4176,plain,
% 3.60/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 3.60/0.99      | k2_funct_1(sK2) = X0
% 3.60/0.99      | k1_relat_1(X0) != sK1
% 3.60/0.99      | v1_relat_1(X0) != iProver_top
% 3.60/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.60/0.99      inference(light_normalisation,[status(thm)],[c_3112,c_3737]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_7743,plain,
% 3.60/0.99      ( k2_funct_1(sK2) = sK3
% 3.60/0.99      | k1_relat_1(sK3) != sK1
% 3.60/0.99      | v1_relat_1(sK3) != iProver_top
% 3.60/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_7739,c_4176]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_14,plain,
% 3.60/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.60/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.60/0.99      | k1_xboole_0 = X2 ),
% 3.60/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1227,plain,
% 3.60/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.60/0.99      | k1_xboole_0 = X1
% 3.60/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3688,plain,
% 3.60/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.60/0.99      | sK0 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1223,c_1227]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_6,plain,
% 3.60/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.60/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1233,plain,
% 3.60/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.60/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_2449,plain,
% 3.60/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.60/0.99      inference(superposition,[status(thm)],[c_1223,c_1233]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_3708,plain,
% 3.60/0.99      ( k1_relat_1(sK3) = sK1
% 3.60/0.99      | sK0 = k1_xboole_0
% 3.60/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.60/0.99      inference(demodulation,[status(thm)],[c_3688,c_2449]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1534,plain,
% 3.60/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_754]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1535,plain,
% 3.60/0.99      ( sK0 != k1_xboole_0
% 3.60/0.99      | k1_xboole_0 = sK0
% 3.60/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_1534]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1504,plain,
% 3.60/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.60/0.99      | v1_relat_1(sK3) ),
% 3.60/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_1505,plain,
% 3.60/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.60/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_1504]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_23,negated_conjecture,
% 3.60/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.60/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_25,negated_conjecture,
% 3.60/0.99      ( k1_xboole_0 != sK0 ),
% 3.60/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_30,negated_conjecture,
% 3.60/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.60/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(c_39,plain,
% 3.60/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.60/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.60/0.99  
% 3.60/0.99  cnf(contradiction,plain,
% 3.60/0.99      ( $false ),
% 3.60/0.99      inference(minisat,
% 3.60/0.99                [status(thm)],
% 3.60/0.99                [c_7743,c_3708,c_1535,c_1505,c_784,c_23,c_25,c_40,c_39,
% 3.60/0.99                 c_38]) ).
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.60/0.99  
% 3.60/0.99  ------                               Statistics
% 3.60/0.99  
% 3.60/0.99  ------ General
% 3.60/0.99  
% 3.60/0.99  abstr_ref_over_cycles:                  0
% 3.60/0.99  abstr_ref_under_cycles:                 0
% 3.60/0.99  gc_basic_clause_elim:                   0
% 3.60/0.99  forced_gc_time:                         0
% 3.60/0.99  parsing_time:                           0.014
% 3.60/0.99  unif_index_cands_time:                  0.
% 3.60/0.99  unif_index_add_time:                    0.
% 3.60/0.99  orderings_time:                         0.
% 3.60/0.99  out_proof_time:                         0.021
% 3.60/0.99  total_time:                             0.386
% 3.60/0.99  num_of_symbols:                         52
% 3.60/0.99  num_of_terms:                           7316
% 3.60/0.99  
% 3.60/0.99  ------ Preprocessing
% 3.60/0.99  
% 3.60/0.99  num_of_splits:                          0
% 3.60/0.99  num_of_split_atoms:                     0
% 3.60/0.99  num_of_reused_defs:                     0
% 3.60/0.99  num_eq_ax_congr_red:                    7
% 3.60/0.99  num_of_sem_filtered_clauses:            1
% 3.60/0.99  num_of_subtypes:                        0
% 3.60/0.99  monotx_restored_types:                  0
% 3.60/0.99  sat_num_of_epr_types:                   0
% 3.60/0.99  sat_num_of_non_cyclic_types:            0
% 3.60/0.99  sat_guarded_non_collapsed_types:        0
% 3.60/0.99  num_pure_diseq_elim:                    0
% 3.60/0.99  simp_replaced_by:                       0
% 3.60/0.99  res_preprocessed:                       164
% 3.60/0.99  prep_upred:                             0
% 3.60/0.99  prep_unflattend:                        16
% 3.60/0.99  smt_new_axioms:                         0
% 3.60/0.99  pred_elim_cands:                        4
% 3.60/0.99  pred_elim:                              2
% 3.60/0.99  pred_elim_cl:                           3
% 3.60/0.99  pred_elim_cycles:                       4
% 3.60/0.99  merged_defs:                            0
% 3.60/0.99  merged_defs_ncl:                        0
% 3.60/0.99  bin_hyper_res:                          0
% 3.60/0.99  prep_cycles:                            4
% 3.60/0.99  pred_elim_time:                         0.01
% 3.60/0.99  splitting_time:                         0.
% 3.60/0.99  sem_filter_time:                        0.
% 3.60/0.99  monotx_time:                            0.
% 3.60/0.99  subtype_inf_time:                       0.
% 3.60/0.99  
% 3.60/0.99  ------ Problem properties
% 3.60/0.99  
% 3.60/0.99  clauses:                                32
% 3.60/0.99  conjectures:                            10
% 3.60/0.99  epr:                                    6
% 3.60/0.99  horn:                                   26
% 3.60/0.99  ground:                                 13
% 3.60/0.99  unary:                                  12
% 3.60/0.99  binary:                                 4
% 3.60/0.99  lits:                                   87
% 3.60/0.99  lits_eq:                                32
% 3.60/0.99  fd_pure:                                0
% 3.60/0.99  fd_pseudo:                              0
% 3.60/0.99  fd_cond:                                6
% 3.60/0.99  fd_pseudo_cond:                         0
% 3.60/0.99  ac_symbols:                             0
% 3.60/0.99  
% 3.60/0.99  ------ Propositional Solver
% 3.60/0.99  
% 3.60/0.99  prop_solver_calls:                      27
% 3.60/0.99  prop_fast_solver_calls:                 1260
% 3.60/0.99  smt_solver_calls:                       0
% 3.60/0.99  smt_fast_solver_calls:                  0
% 3.60/0.99  prop_num_of_clauses:                    3105
% 3.60/0.99  prop_preprocess_simplified:             8925
% 3.60/0.99  prop_fo_subsumed:                       56
% 3.60/0.99  prop_solver_time:                       0.
% 3.60/0.99  smt_solver_time:                        0.
% 3.60/0.99  smt_fast_solver_time:                   0.
% 3.60/0.99  prop_fast_solver_time:                  0.
% 3.60/0.99  prop_unsat_core_time:                   0.
% 3.60/0.99  
% 3.60/0.99  ------ QBF
% 3.60/0.99  
% 3.60/0.99  qbf_q_res:                              0
% 3.60/0.99  qbf_num_tautologies:                    0
% 3.60/0.99  qbf_prep_cycles:                        0
% 3.60/0.99  
% 3.60/0.99  ------ BMC1
% 3.60/0.99  
% 3.60/0.99  bmc1_current_bound:                     -1
% 3.60/0.99  bmc1_last_solved_bound:                 -1
% 3.60/0.99  bmc1_unsat_core_size:                   -1
% 3.60/0.99  bmc1_unsat_core_parents_size:           -1
% 3.60/0.99  bmc1_merge_next_fun:                    0
% 3.60/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.60/0.99  
% 3.60/0.99  ------ Instantiation
% 3.60/0.99  
% 3.60/0.99  inst_num_of_clauses:                    941
% 3.60/0.99  inst_num_in_passive:                    415
% 3.60/0.99  inst_num_in_active:                     396
% 3.60/0.99  inst_num_in_unprocessed:                130
% 3.60/0.99  inst_num_of_loops:                      400
% 3.60/0.99  inst_num_of_learning_restarts:          0
% 3.60/0.99  inst_num_moves_active_passive:          3
% 3.60/0.99  inst_lit_activity:                      0
% 3.60/0.99  inst_lit_activity_moves:                0
% 3.60/0.99  inst_num_tautologies:                   0
% 3.60/0.99  inst_num_prop_implied:                  0
% 3.60/0.99  inst_num_existing_simplified:           0
% 3.60/0.99  inst_num_eq_res_simplified:             0
% 3.60/0.99  inst_num_child_elim:                    0
% 3.60/0.99  inst_num_of_dismatching_blockings:      15
% 3.60/0.99  inst_num_of_non_proper_insts:           636
% 3.60/0.99  inst_num_of_duplicates:                 0
% 3.60/0.99  inst_inst_num_from_inst_to_res:         0
% 3.60/0.99  inst_dismatching_checking_time:         0.
% 3.60/0.99  
% 3.60/0.99  ------ Resolution
% 3.60/0.99  
% 3.60/0.99  res_num_of_clauses:                     0
% 3.60/0.99  res_num_in_passive:                     0
% 3.60/0.99  res_num_in_active:                      0
% 3.60/0.99  res_num_of_loops:                       168
% 3.60/0.99  res_forward_subset_subsumed:            79
% 3.60/0.99  res_backward_subset_subsumed:           0
% 3.60/0.99  res_forward_subsumed:                   0
% 3.60/0.99  res_backward_subsumed:                  0
% 3.60/0.99  res_forward_subsumption_resolution:     0
% 3.60/0.99  res_backward_subsumption_resolution:    0
% 3.60/0.99  res_clause_to_clause_subsumption:       169
% 3.60/0.99  res_orphan_elimination:                 0
% 3.60/0.99  res_tautology_del:                      31
% 3.60/0.99  res_num_eq_res_simplified:              0
% 3.60/0.99  res_num_sel_changes:                    0
% 3.60/0.99  res_moves_from_active_to_pass:          0
% 3.60/0.99  
% 3.60/0.99  ------ Superposition
% 3.60/0.99  
% 3.60/0.99  sup_time_total:                         0.
% 3.60/0.99  sup_time_generating:                    0.
% 3.60/0.99  sup_time_sim_full:                      0.
% 3.60/0.99  sup_time_sim_immed:                     0.
% 3.60/0.99  
% 3.60/0.99  sup_num_of_clauses:                     116
% 3.60/0.99  sup_num_in_active:                      69
% 3.60/0.99  sup_num_in_passive:                     47
% 3.60/0.99  sup_num_of_loops:                       79
% 3.60/0.99  sup_fw_superposition:                   35
% 3.60/0.99  sup_bw_superposition:                   59
% 3.60/0.99  sup_immediate_simplified:               15
% 3.60/0.99  sup_given_eliminated:                   2
% 3.60/0.99  comparisons_done:                       0
% 3.60/0.99  comparisons_avoided:                    0
% 3.60/0.99  
% 3.60/0.99  ------ Simplifications
% 3.60/0.99  
% 3.60/0.99  
% 3.60/0.99  sim_fw_subset_subsumed:                 4
% 3.60/0.99  sim_bw_subset_subsumed:                 2
% 3.60/0.99  sim_fw_subsumed:                        0
% 3.60/0.99  sim_bw_subsumed:                        0
% 3.60/0.99  sim_fw_subsumption_res:                 0
% 3.60/0.99  sim_bw_subsumption_res:                 0
% 3.60/0.99  sim_tautology_del:                      0
% 3.60/0.99  sim_eq_tautology_del:                   6
% 3.60/0.99  sim_eq_res_simp:                        0
% 3.60/0.99  sim_fw_demodulated:                     13
% 3.60/0.99  sim_bw_demodulated:                     11
% 3.60/0.99  sim_light_normalised:                   3
% 3.60/0.99  sim_joinable_taut:                      0
% 3.60/0.99  sim_joinable_simp:                      0
% 3.60/0.99  sim_ac_normalised:                      0
% 3.60/0.99  sim_smt_subsumption:                    0
% 3.60/0.99  
%------------------------------------------------------------------------------
