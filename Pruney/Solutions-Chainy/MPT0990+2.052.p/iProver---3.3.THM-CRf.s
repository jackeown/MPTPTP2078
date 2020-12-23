%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:07 EST 2020

% Result     : Theorem 3.26s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 881 expanded)
%              Number of clauses        :  117 ( 245 expanded)
%              Number of leaves         :   16 ( 231 expanded)
%              Depth                    :   25
%              Number of atoms          :  733 (8188 expanded)
%              Number of equality atoms :  372 (2985 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
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

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f36,plain,(
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

fof(f35,plain,
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

fof(f37,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f25])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f59,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f19])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f66,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f65,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f10,axiom,(
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

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f69,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f9,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f68,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f37])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1145,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1148,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1149,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3618,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1149])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_35,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3884,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3618,c_35])).

cnf(c_3885,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3884])).

cnf(c_3895,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_3885])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1524,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1795,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1524])).

cnf(c_2078,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1795])).

cnf(c_2144,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2078])).

cnf(c_4075,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3895,c_31,c_29,c_28,c_26,c_2144])).

cnf(c_5,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_24])).

cnf(c_319,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_318])).

cnf(c_1142,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_319])).

cnf(c_4078,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4075,c_1142])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_389,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_390,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_389])).

cnf(c_394,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_390,c_31])).

cnf(c_395,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_394])).

cnf(c_1383,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_395])).

cnf(c_1384,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1383])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_437,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_23])).

cnf(c_438,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_442,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_31])).

cnf(c_443,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_1409,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_443])).

cnf(c_1410,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1151,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4080,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4075,c_1151])).

cnf(c_1137,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_443])).

cnf(c_2076,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1137])).

cnf(c_2254,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2076,c_33,c_34,c_25,c_1410])).

cnf(c_3620,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2254,c_1149])).

cnf(c_4380,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3620,c_33,c_34,c_25,c_1384])).

cnf(c_4381,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4380])).

cnf(c_4391,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_4381])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_335,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_23])).

cnf(c_336,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_335])).

cnf(c_340,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_336,c_31])).

cnf(c_341,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_340])).

cnf(c_1141,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_341])).

cnf(c_2590,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_25,c_1141])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1386,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_341])).

cnf(c_1670,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1386])).

cnf(c_2969,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2590,c_30,c_29,c_25,c_21,c_1670])).

cnf(c_4399,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4391,c_2969])).

cnf(c_4473,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4399,c_32])).

cnf(c_4476,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4473,c_1151])).

cnf(c_6699,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4078,c_32,c_33,c_34,c_35,c_37,c_25,c_1384,c_1410,c_4080,c_4476])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1152,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2641,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1145,c_1152])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1159,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2135,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1145,c_1159])).

cnf(c_2653,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2641,c_2135])).

cnf(c_696,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_727,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_697,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1448,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_1449,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3407,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2653,c_33,c_21,c_727,c_1449])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1158,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1715,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1145,c_1158])).

cnf(c_1717,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1715,c_25])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k2_relat_1(X1) != k1_relat_1(X0)
    | k2_funct_1(X1) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_461,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_relat_1(X0) != k1_relat_1(X1)
    | k2_funct_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_23])).

cnf(c_462,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_461])).

cnf(c_466,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_462,c_31])).

cnf(c_467,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0 ),
    inference(renaming,[status(thm)],[c_466])).

cnf(c_1136,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_468,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1421,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1422,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1421])).

cnf(c_1572,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_funct_1(sK2) = X0
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1136,c_34,c_468,c_1422])).

cnf(c_1573,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(X0)
    | k2_funct_1(sK2) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1572])).

cnf(c_1722,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1717,c_1573])).

cnf(c_3411,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3407,c_1722])).

cnf(c_6775,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6699,c_3411])).

cnf(c_2640,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1152])).

cnf(c_2134,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1148,c_1159])).

cnf(c_2660,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2640,c_2134])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_36,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1450,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_1451,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_5905,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2660,c_36,c_22,c_727,c_1451])).

cnf(c_6780,plain,
    ( k2_funct_1(sK2) = sK3
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6775,c_5905])).

cnf(c_6781,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_6780])).

cnf(c_1418,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1419,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1418])).

cnf(c_20,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6781,c_1419,c_20,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:00:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.26/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/0.98  
% 3.26/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.26/0.98  
% 3.26/0.98  ------  iProver source info
% 3.26/0.98  
% 3.26/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.26/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.26/0.98  git: non_committed_changes: false
% 3.26/0.98  git: last_make_outside_of_git: false
% 3.26/0.98  
% 3.26/0.98  ------ 
% 3.26/0.98  
% 3.26/0.98  ------ Input Options
% 3.26/0.98  
% 3.26/0.98  --out_options                           all
% 3.26/0.98  --tptp_safe_out                         true
% 3.26/0.98  --problem_path                          ""
% 3.26/0.98  --include_path                          ""
% 3.26/0.98  --clausifier                            res/vclausify_rel
% 3.26/0.98  --clausifier_options                    --mode clausify
% 3.26/0.98  --stdin                                 false
% 3.26/0.98  --stats_out                             all
% 3.26/0.98  
% 3.26/0.98  ------ General Options
% 3.26/0.98  
% 3.26/0.98  --fof                                   false
% 3.26/0.98  --time_out_real                         305.
% 3.26/0.98  --time_out_virtual                      -1.
% 3.26/0.98  --symbol_type_check                     false
% 3.26/0.98  --clausify_out                          false
% 3.26/0.98  --sig_cnt_out                           false
% 3.26/0.98  --trig_cnt_out                          false
% 3.26/0.98  --trig_cnt_out_tolerance                1.
% 3.26/0.98  --trig_cnt_out_sk_spl                   false
% 3.26/0.98  --abstr_cl_out                          false
% 3.26/0.98  
% 3.26/0.98  ------ Global Options
% 3.26/0.98  
% 3.26/0.98  --schedule                              default
% 3.26/0.98  --add_important_lit                     false
% 3.26/0.98  --prop_solver_per_cl                    1000
% 3.26/0.98  --min_unsat_core                        false
% 3.26/0.98  --soft_assumptions                      false
% 3.26/0.98  --soft_lemma_size                       3
% 3.26/0.98  --prop_impl_unit_size                   0
% 3.26/0.98  --prop_impl_unit                        []
% 3.26/0.98  --share_sel_clauses                     true
% 3.26/0.98  --reset_solvers                         false
% 3.26/0.98  --bc_imp_inh                            [conj_cone]
% 3.26/0.98  --conj_cone_tolerance                   3.
% 3.26/0.98  --extra_neg_conj                        none
% 3.26/0.98  --large_theory_mode                     true
% 3.26/0.98  --prolific_symb_bound                   200
% 3.26/0.98  --lt_threshold                          2000
% 3.26/0.98  --clause_weak_htbl                      true
% 3.26/0.98  --gc_record_bc_elim                     false
% 3.26/0.98  
% 3.26/0.98  ------ Preprocessing Options
% 3.26/0.98  
% 3.26/0.98  --preprocessing_flag                    true
% 3.26/0.98  --time_out_prep_mult                    0.1
% 3.26/0.98  --splitting_mode                        input
% 3.26/0.98  --splitting_grd                         true
% 3.26/0.98  --splitting_cvd                         false
% 3.26/0.98  --splitting_cvd_svl                     false
% 3.26/0.98  --splitting_nvd                         32
% 3.26/0.98  --sub_typing                            true
% 3.26/0.98  --prep_gs_sim                           true
% 3.26/0.98  --prep_unflatten                        true
% 3.26/0.98  --prep_res_sim                          true
% 3.26/0.98  --prep_upred                            true
% 3.26/0.98  --prep_sem_filter                       exhaustive
% 3.26/0.98  --prep_sem_filter_out                   false
% 3.26/0.98  --pred_elim                             true
% 3.26/0.98  --res_sim_input                         true
% 3.26/0.98  --eq_ax_congr_red                       true
% 3.26/0.98  --pure_diseq_elim                       true
% 3.26/0.98  --brand_transform                       false
% 3.26/0.98  --non_eq_to_eq                          false
% 3.26/0.98  --prep_def_merge                        true
% 3.26/0.98  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     num_symb
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       true
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  ------ Parsing...
% 3.26/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.26/0.99  ------ Proving...
% 3.26/0.99  ------ Problem Properties 
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  clauses                                 29
% 3.26/0.99  conjectures                             10
% 3.26/0.99  EPR                                     6
% 3.26/0.99  Horn                                    23
% 3.26/0.99  unary                                   10
% 3.26/0.99  binary                                  3
% 3.26/0.99  lits                                    83
% 3.26/0.99  lits eq                                 29
% 3.26/0.99  fd_pure                                 0
% 3.26/0.99  fd_pseudo                               0
% 3.26/0.99  fd_cond                                 6
% 3.26/0.99  fd_pseudo_cond                          0
% 3.26/0.99  AC symbols                              0
% 3.26/0.99  
% 3.26/0.99  ------ Schedule dynamic 5 is on 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ 
% 3.26/0.99  Current options:
% 3.26/0.99  ------ 
% 3.26/0.99  
% 3.26/0.99  ------ Input Options
% 3.26/0.99  
% 3.26/0.99  --out_options                           all
% 3.26/0.99  --tptp_safe_out                         true
% 3.26/0.99  --problem_path                          ""
% 3.26/0.99  --include_path                          ""
% 3.26/0.99  --clausifier                            res/vclausify_rel
% 3.26/0.99  --clausifier_options                    --mode clausify
% 3.26/0.99  --stdin                                 false
% 3.26/0.99  --stats_out                             all
% 3.26/0.99  
% 3.26/0.99  ------ General Options
% 3.26/0.99  
% 3.26/0.99  --fof                                   false
% 3.26/0.99  --time_out_real                         305.
% 3.26/0.99  --time_out_virtual                      -1.
% 3.26/0.99  --symbol_type_check                     false
% 3.26/0.99  --clausify_out                          false
% 3.26/0.99  --sig_cnt_out                           false
% 3.26/0.99  --trig_cnt_out                          false
% 3.26/0.99  --trig_cnt_out_tolerance                1.
% 3.26/0.99  --trig_cnt_out_sk_spl                   false
% 3.26/0.99  --abstr_cl_out                          false
% 3.26/0.99  
% 3.26/0.99  ------ Global Options
% 3.26/0.99  
% 3.26/0.99  --schedule                              default
% 3.26/0.99  --add_important_lit                     false
% 3.26/0.99  --prop_solver_per_cl                    1000
% 3.26/0.99  --min_unsat_core                        false
% 3.26/0.99  --soft_assumptions                      false
% 3.26/0.99  --soft_lemma_size                       3
% 3.26/0.99  --prop_impl_unit_size                   0
% 3.26/0.99  --prop_impl_unit                        []
% 3.26/0.99  --share_sel_clauses                     true
% 3.26/0.99  --reset_solvers                         false
% 3.26/0.99  --bc_imp_inh                            [conj_cone]
% 3.26/0.99  --conj_cone_tolerance                   3.
% 3.26/0.99  --extra_neg_conj                        none
% 3.26/0.99  --large_theory_mode                     true
% 3.26/0.99  --prolific_symb_bound                   200
% 3.26/0.99  --lt_threshold                          2000
% 3.26/0.99  --clause_weak_htbl                      true
% 3.26/0.99  --gc_record_bc_elim                     false
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing Options
% 3.26/0.99  
% 3.26/0.99  --preprocessing_flag                    true
% 3.26/0.99  --time_out_prep_mult                    0.1
% 3.26/0.99  --splitting_mode                        input
% 3.26/0.99  --splitting_grd                         true
% 3.26/0.99  --splitting_cvd                         false
% 3.26/0.99  --splitting_cvd_svl                     false
% 3.26/0.99  --splitting_nvd                         32
% 3.26/0.99  --sub_typing                            true
% 3.26/0.99  --prep_gs_sim                           true
% 3.26/0.99  --prep_unflatten                        true
% 3.26/0.99  --prep_res_sim                          true
% 3.26/0.99  --prep_upred                            true
% 3.26/0.99  --prep_sem_filter                       exhaustive
% 3.26/0.99  --prep_sem_filter_out                   false
% 3.26/0.99  --pred_elim                             true
% 3.26/0.99  --res_sim_input                         true
% 3.26/0.99  --eq_ax_congr_red                       true
% 3.26/0.99  --pure_diseq_elim                       true
% 3.26/0.99  --brand_transform                       false
% 3.26/0.99  --non_eq_to_eq                          false
% 3.26/0.99  --prep_def_merge                        true
% 3.26/0.99  --prep_def_merge_prop_impl              false
% 3.26/0.99  --prep_def_merge_mbd                    true
% 3.26/0.99  --prep_def_merge_tr_red                 false
% 3.26/0.99  --prep_def_merge_tr_cl                  false
% 3.26/0.99  --smt_preprocessing                     true
% 3.26/0.99  --smt_ac_axioms                         fast
% 3.26/0.99  --preprocessed_out                      false
% 3.26/0.99  --preprocessed_stats                    false
% 3.26/0.99  
% 3.26/0.99  ------ Abstraction refinement Options
% 3.26/0.99  
% 3.26/0.99  --abstr_ref                             []
% 3.26/0.99  --abstr_ref_prep                        false
% 3.26/0.99  --abstr_ref_until_sat                   false
% 3.26/0.99  --abstr_ref_sig_restrict                funpre
% 3.26/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.26/0.99  --abstr_ref_under                       []
% 3.26/0.99  
% 3.26/0.99  ------ SAT Options
% 3.26/0.99  
% 3.26/0.99  --sat_mode                              false
% 3.26/0.99  --sat_fm_restart_options                ""
% 3.26/0.99  --sat_gr_def                            false
% 3.26/0.99  --sat_epr_types                         true
% 3.26/0.99  --sat_non_cyclic_types                  false
% 3.26/0.99  --sat_finite_models                     false
% 3.26/0.99  --sat_fm_lemmas                         false
% 3.26/0.99  --sat_fm_prep                           false
% 3.26/0.99  --sat_fm_uc_incr                        true
% 3.26/0.99  --sat_out_model                         small
% 3.26/0.99  --sat_out_clauses                       false
% 3.26/0.99  
% 3.26/0.99  ------ QBF Options
% 3.26/0.99  
% 3.26/0.99  --qbf_mode                              false
% 3.26/0.99  --qbf_elim_univ                         false
% 3.26/0.99  --qbf_dom_inst                          none
% 3.26/0.99  --qbf_dom_pre_inst                      false
% 3.26/0.99  --qbf_sk_in                             false
% 3.26/0.99  --qbf_pred_elim                         true
% 3.26/0.99  --qbf_split                             512
% 3.26/0.99  
% 3.26/0.99  ------ BMC1 Options
% 3.26/0.99  
% 3.26/0.99  --bmc1_incremental                      false
% 3.26/0.99  --bmc1_axioms                           reachable_all
% 3.26/0.99  --bmc1_min_bound                        0
% 3.26/0.99  --bmc1_max_bound                        -1
% 3.26/0.99  --bmc1_max_bound_default                -1
% 3.26/0.99  --bmc1_symbol_reachability              true
% 3.26/0.99  --bmc1_property_lemmas                  false
% 3.26/0.99  --bmc1_k_induction                      false
% 3.26/0.99  --bmc1_non_equiv_states                 false
% 3.26/0.99  --bmc1_deadlock                         false
% 3.26/0.99  --bmc1_ucm                              false
% 3.26/0.99  --bmc1_add_unsat_core                   none
% 3.26/0.99  --bmc1_unsat_core_children              false
% 3.26/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.26/0.99  --bmc1_out_stat                         full
% 3.26/0.99  --bmc1_ground_init                      false
% 3.26/0.99  --bmc1_pre_inst_next_state              false
% 3.26/0.99  --bmc1_pre_inst_state                   false
% 3.26/0.99  --bmc1_pre_inst_reach_state             false
% 3.26/0.99  --bmc1_out_unsat_core                   false
% 3.26/0.99  --bmc1_aig_witness_out                  false
% 3.26/0.99  --bmc1_verbose                          false
% 3.26/0.99  --bmc1_dump_clauses_tptp                false
% 3.26/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.26/0.99  --bmc1_dump_file                        -
% 3.26/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.26/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.26/0.99  --bmc1_ucm_extend_mode                  1
% 3.26/0.99  --bmc1_ucm_init_mode                    2
% 3.26/0.99  --bmc1_ucm_cone_mode                    none
% 3.26/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.26/0.99  --bmc1_ucm_relax_model                  4
% 3.26/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.26/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.26/0.99  --bmc1_ucm_layered_model                none
% 3.26/0.99  --bmc1_ucm_max_lemma_size               10
% 3.26/0.99  
% 3.26/0.99  ------ AIG Options
% 3.26/0.99  
% 3.26/0.99  --aig_mode                              false
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation Options
% 3.26/0.99  
% 3.26/0.99  --instantiation_flag                    true
% 3.26/0.99  --inst_sos_flag                         false
% 3.26/0.99  --inst_sos_phase                        true
% 3.26/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.26/0.99  --inst_lit_sel_side                     none
% 3.26/0.99  --inst_solver_per_active                1400
% 3.26/0.99  --inst_solver_calls_frac                1.
% 3.26/0.99  --inst_passive_queue_type               priority_queues
% 3.26/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.26/0.99  --inst_passive_queues_freq              [25;2]
% 3.26/0.99  --inst_dismatching                      true
% 3.26/0.99  --inst_eager_unprocessed_to_passive     true
% 3.26/0.99  --inst_prop_sim_given                   true
% 3.26/0.99  --inst_prop_sim_new                     false
% 3.26/0.99  --inst_subs_new                         false
% 3.26/0.99  --inst_eq_res_simp                      false
% 3.26/0.99  --inst_subs_given                       false
% 3.26/0.99  --inst_orphan_elimination               true
% 3.26/0.99  --inst_learning_loop_flag               true
% 3.26/0.99  --inst_learning_start                   3000
% 3.26/0.99  --inst_learning_factor                  2
% 3.26/0.99  --inst_start_prop_sim_after_learn       3
% 3.26/0.99  --inst_sel_renew                        solver
% 3.26/0.99  --inst_lit_activity_flag                true
% 3.26/0.99  --inst_restr_to_given                   false
% 3.26/0.99  --inst_activity_threshold               500
% 3.26/0.99  --inst_out_proof                        true
% 3.26/0.99  
% 3.26/0.99  ------ Resolution Options
% 3.26/0.99  
% 3.26/0.99  --resolution_flag                       false
% 3.26/0.99  --res_lit_sel                           adaptive
% 3.26/0.99  --res_lit_sel_side                      none
% 3.26/0.99  --res_ordering                          kbo
% 3.26/0.99  --res_to_prop_solver                    active
% 3.26/0.99  --res_prop_simpl_new                    false
% 3.26/0.99  --res_prop_simpl_given                  true
% 3.26/0.99  --res_passive_queue_type                priority_queues
% 3.26/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.26/0.99  --res_passive_queues_freq               [15;5]
% 3.26/0.99  --res_forward_subs                      full
% 3.26/0.99  --res_backward_subs                     full
% 3.26/0.99  --res_forward_subs_resolution           true
% 3.26/0.99  --res_backward_subs_resolution          true
% 3.26/0.99  --res_orphan_elimination                true
% 3.26/0.99  --res_time_limit                        2.
% 3.26/0.99  --res_out_proof                         true
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Options
% 3.26/0.99  
% 3.26/0.99  --superposition_flag                    true
% 3.26/0.99  --sup_passive_queue_type                priority_queues
% 3.26/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.26/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.26/0.99  --demod_completeness_check              fast
% 3.26/0.99  --demod_use_ground                      true
% 3.26/0.99  --sup_to_prop_solver                    passive
% 3.26/0.99  --sup_prop_simpl_new                    true
% 3.26/0.99  --sup_prop_simpl_given                  true
% 3.26/0.99  --sup_fun_splitting                     false
% 3.26/0.99  --sup_smt_interval                      50000
% 3.26/0.99  
% 3.26/0.99  ------ Superposition Simplification Setup
% 3.26/0.99  
% 3.26/0.99  --sup_indices_passive                   []
% 3.26/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.26/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.26/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_full_bw                           [BwDemod]
% 3.26/0.99  --sup_immed_triv                        [TrivRules]
% 3.26/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.26/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_immed_bw_main                     []
% 3.26/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.26/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.26/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.26/0.99  
% 3.26/0.99  ------ Combination Options
% 3.26/0.99  
% 3.26/0.99  --comb_res_mult                         3
% 3.26/0.99  --comb_sup_mult                         2
% 3.26/0.99  --comb_inst_mult                        10
% 3.26/0.99  
% 3.26/0.99  ------ Debug Options
% 3.26/0.99  
% 3.26/0.99  --dbg_backtrace                         false
% 3.26/0.99  --dbg_dump_prop_clauses                 false
% 3.26/0.99  --dbg_dump_prop_clauses_file            -
% 3.26/0.99  --dbg_out_stat                          false
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  ------ Proving...
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS status Theorem for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  fof(f12,conjecture,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f13,negated_conjecture,(
% 3.26/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.26/0.99    inference(negated_conjecture,[],[f12])).
% 3.26/0.99  
% 3.26/0.99  fof(f31,plain,(
% 3.26/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.26/0.99    inference(ennf_transformation,[],[f13])).
% 3.26/0.99  
% 3.26/0.99  fof(f32,plain,(
% 3.26/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.26/0.99    inference(flattening,[],[f31])).
% 3.26/0.99  
% 3.26/0.99  fof(f36,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f35,plain,(
% 3.26/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.26/0.99    introduced(choice_axiom,[])).
% 3.26/0.99  
% 3.26/0.99  fof(f37,plain,(
% 3.26/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.26/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f36,f35])).
% 3.26/0.99  
% 3.26/0.99  fof(f61,plain,(
% 3.26/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f64,plain,(
% 3.26/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f8,axiom,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f25,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.26/0.99    inference(ennf_transformation,[],[f8])).
% 3.26/0.99  
% 3.26/0.99  fof(f26,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.26/0.99    inference(flattening,[],[f25])).
% 3.26/0.99  
% 3.26/0.99  fof(f52,plain,(
% 3.26/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f26])).
% 3.26/0.99  
% 3.26/0.99  fof(f62,plain,(
% 3.26/0.99    v1_funct_1(sK3)),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f59,plain,(
% 3.26/0.99    v1_funct_1(sK2)),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f5,axiom,(
% 3.26/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f19,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.26/0.99    inference(ennf_transformation,[],[f5])).
% 3.26/0.99  
% 3.26/0.99  fof(f20,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(flattening,[],[f19])).
% 3.26/0.99  
% 3.26/0.99  fof(f33,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(nnf_transformation,[],[f20])).
% 3.26/0.99  
% 3.26/0.99  fof(f42,plain,(
% 3.26/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f33])).
% 3.26/0.99  
% 3.26/0.99  fof(f66,plain,(
% 3.26/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f60,plain,(
% 3.26/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f65,plain,(
% 3.26/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f10,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f27,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.26/0.99    inference(ennf_transformation,[],[f10])).
% 3.26/0.99  
% 3.26/0.99  fof(f28,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.26/0.99    inference(flattening,[],[f27])).
% 3.26/0.99  
% 3.26/0.99  fof(f54,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f28])).
% 3.26/0.99  
% 3.26/0.99  fof(f67,plain,(
% 3.26/0.99    v2_funct_1(sK2)),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f56,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f28])).
% 3.26/0.99  
% 3.26/0.99  fof(f7,axiom,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f23,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.26/0.99    inference(ennf_transformation,[],[f7])).
% 3.26/0.99  
% 3.26/0.99  fof(f24,plain,(
% 3.26/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.26/0.99    inference(flattening,[],[f23])).
% 3.26/0.99  
% 3.26/0.99  fof(f51,plain,(
% 3.26/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f24])).
% 3.26/0.99  
% 3.26/0.99  fof(f11,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f29,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.26/0.99    inference(ennf_transformation,[],[f11])).
% 3.26/0.99  
% 3.26/0.99  fof(f30,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.26/0.99    inference(flattening,[],[f29])).
% 3.26/0.99  
% 3.26/0.99  fof(f57,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f30])).
% 3.26/0.99  
% 3.26/0.99  fof(f69,plain,(
% 3.26/0.99    k1_xboole_0 != sK1),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f6,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f21,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(ennf_transformation,[],[f6])).
% 3.26/0.99  
% 3.26/0.99  fof(f22,plain,(
% 3.26/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(flattening,[],[f21])).
% 3.26/0.99  
% 3.26/0.99  fof(f34,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(nnf_transformation,[],[f22])).
% 3.26/0.99  
% 3.26/0.99  fof(f44,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f34])).
% 3.26/0.99  
% 3.26/0.99  fof(f3,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f17,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(ennf_transformation,[],[f3])).
% 3.26/0.99  
% 3.26/0.99  fof(f40,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f17])).
% 3.26/0.99  
% 3.26/0.99  fof(f4,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f18,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(ennf_transformation,[],[f4])).
% 3.26/0.99  
% 3.26/0.99  fof(f41,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f18])).
% 3.26/0.99  
% 3.26/0.99  fof(f1,axiom,(
% 3.26/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f14,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.26/0.99    inference(ennf_transformation,[],[f1])).
% 3.26/0.99  
% 3.26/0.99  fof(f15,plain,(
% 3.26/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.26/0.99    inference(flattening,[],[f14])).
% 3.26/0.99  
% 3.26/0.99  fof(f38,plain,(
% 3.26/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f15])).
% 3.26/0.99  
% 3.26/0.99  fof(f9,axiom,(
% 3.26/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f53,plain,(
% 3.26/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.26/0.99    inference(cnf_transformation,[],[f9])).
% 3.26/0.99  
% 3.26/0.99  fof(f71,plain,(
% 3.26/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.26/0.99    inference(definition_unfolding,[],[f38,f53])).
% 3.26/0.99  
% 3.26/0.99  fof(f2,axiom,(
% 3.26/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.26/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.26/0.99  
% 3.26/0.99  fof(f16,plain,(
% 3.26/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.26/0.99    inference(ennf_transformation,[],[f2])).
% 3.26/0.99  
% 3.26/0.99  fof(f39,plain,(
% 3.26/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.26/0.99    inference(cnf_transformation,[],[f16])).
% 3.26/0.99  
% 3.26/0.99  fof(f63,plain,(
% 3.26/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f68,plain,(
% 3.26/0.99    k1_xboole_0 != sK0),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  fof(f70,plain,(
% 3.26/0.99    k2_funct_1(sK2) != sK3),
% 3.26/0.99    inference(cnf_transformation,[],[f37])).
% 3.26/0.99  
% 3.26/0.99  cnf(c_29,negated_conjecture,
% 3.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.26/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1145,plain,
% 3.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_26,negated_conjecture,
% 3.26/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.26/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1148,plain,
% 3.26/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_14,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(X3)
% 3.26/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1149,plain,
% 3.26/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.26/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.26/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | v1_funct_1(X5) != iProver_top
% 3.26/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3618,plain,
% 3.26/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | v1_funct_1(X2) != iProver_top
% 3.26/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1148,c_1149]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_28,negated_conjecture,
% 3.26/0.99      ( v1_funct_1(sK3) ),
% 3.26/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_35,plain,
% 3.26/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3884,plain,
% 3.26/0.99      ( v1_funct_1(X2) != iProver_top
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_3618,c_35]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3885,plain,
% 3.26/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_3884]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3895,plain,
% 3.26/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1145,c_3885]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_31,negated_conjecture,
% 3.26/0.99      ( v1_funct_1(sK2) ),
% 3.26/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1524,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(sK3)
% 3.26/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1795,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.26/0.99      | ~ v1_funct_1(sK3)
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1524]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2078,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_1(sK3)
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1795]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2144,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.26/0.99      | ~ v1_funct_1(sK3)
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_2078]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4075,plain,
% 3.26/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_3895,c_31,c_29,c_28,c_26,c_2144]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5,plain,
% 3.26/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.26/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | X3 = X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_24,negated_conjecture,
% 3.26/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.26/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_318,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | X3 = X0
% 3.26/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.26/0.99      | k6_partfun1(sK0) != X3
% 3.26/0.99      | sK0 != X2
% 3.26/0.99      | sK0 != X1 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_5,c_24]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_319,plain,
% 3.26/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.26/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.26/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_318]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1142,plain,
% 3.26/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.26/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.26/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_319]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4078,plain,
% 3.26/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.26/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.26/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_4075,c_1142]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_32,plain,
% 3.26/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_30,negated_conjecture,
% 3.26/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.26/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_33,plain,
% 3.26/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_34,plain,
% 3.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_37,plain,
% 3.26/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_25,negated_conjecture,
% 3.26/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.26/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_17,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.26/0.99      | ~ v2_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_23,negated_conjecture,
% 3.26/0.99      ( v2_funct_1(sK2) ),
% 3.26/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_389,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.26/0.99      | sK2 != X0 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_390,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_389]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_394,plain,
% 3.26/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_390,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_395,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_394]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1383,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.26/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_395]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1384,plain,
% 3.26/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.26/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1383]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_15,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v2_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_437,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.26/0.99      | sK2 != X0 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_23]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_438,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_437]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_442,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.26/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_438,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_443,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_442]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1409,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.26/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_443]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1410,plain,
% 3.26/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.26/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_12,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.26/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(X3) ),
% 3.26/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1151,plain,
% 3.26/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.26/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.26/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top
% 3.26/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4080,plain,
% 3.26/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.26/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.26/0.99      | v1_funct_1(sK3) != iProver_top
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_4075,c_1151]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1137,plain,
% 3.26/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_443]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2076,plain,
% 3.26/0.99      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_25,c_1137]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2254,plain,
% 3.26/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2076,c_33,c_34,c_25,c_1410]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3620,plain,
% 3.26/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | v1_funct_1(X2) != iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_2254,c_1149]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4380,plain,
% 3.26/0.99      ( v1_funct_1(X2) != iProver_top
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_3620,c_33,c_34,c_25,c_1384]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4381,plain,
% 3.26/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.26/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_4380]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4391,plain,
% 3.26/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1145,c_4381]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_19,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v2_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.26/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.26/0.99      | k1_xboole_0 = X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_335,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.26/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.26/0.99      | sK2 != X0
% 3.26/0.99      | k1_xboole_0 = X2 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_23]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_336,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.26/0.99      | k1_xboole_0 = X1 ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_335]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_340,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.26/0.99      | k1_xboole_0 = X1 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_336,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_341,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.26/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.26/0.99      | k1_xboole_0 = X1 ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_340]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1141,plain,
% 3.26/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.26/0.99      | k1_xboole_0 = X1
% 3.26/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_341]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2590,plain,
% 3.26/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.26/0.99      | sK1 = k1_xboole_0
% 3.26/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_25,c_1141]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_21,negated_conjecture,
% 3.26/0.99      ( k1_xboole_0 != sK1 ),
% 3.26/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1386,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.26/0.99      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.26/0.99      | k1_xboole_0 = sK1 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_341]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1670,plain,
% 3.26/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.26/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.26/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.26/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.26/0.99      | k1_xboole_0 = sK1 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1386]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2969,plain,
% 3.26/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2590,c_30,c_29,c_25,c_21,c_1670]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4399,plain,
% 3.26/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_4391,c_2969]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4473,plain,
% 3.26/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_4399,c_32]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_4476,plain,
% 3.26/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.26/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.26/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.26/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.26/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_4473,c_1151]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6699,plain,
% 3.26/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_4078,c_32,c_33,c_34,c_35,c_37,c_25,c_1384,c_1410,
% 3.26/0.99                 c_4080,c_4476]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_11,plain,
% 3.26/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.26/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.26/0.99      | k1_xboole_0 = X2 ),
% 3.26/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1152,plain,
% 3.26/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.26/0.99      | k1_xboole_0 = X1
% 3.26/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2641,plain,
% 3.26/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 3.26/0.99      | sK1 = k1_xboole_0
% 3.26/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1145,c_1152]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1159,plain,
% 3.26/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2135,plain,
% 3.26/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1145,c_1159]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2653,plain,
% 3.26/0.99      ( k1_relat_1(sK2) = sK0
% 3.26/0.99      | sK1 = k1_xboole_0
% 3.26/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_2641,c_2135]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_696,plain,( X0 = X0 ),theory(equality) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_727,plain,
% 3.26/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_696]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_697,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1448,plain,
% 3.26/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_697]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1449,plain,
% 3.26/0.99      ( sK1 != k1_xboole_0
% 3.26/0.99      | k1_xboole_0 = sK1
% 3.26/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1448]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3407,plain,
% 3.26/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2653,c_33,c_21,c_727,c_1449]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1158,plain,
% 3.26/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.26/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1715,plain,
% 3.26/0.99      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1145,c_1158]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1717,plain,
% 3.26/0.99      ( k2_relat_1(sK2) = sK1 ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_1715,c_25]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_0,plain,
% 3.26/0.99      ( ~ v1_relat_1(X0)
% 3.26/0.99      | ~ v1_relat_1(X1)
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(X1)
% 3.26/0.99      | ~ v2_funct_1(X1)
% 3.26/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.26/0.99      | k2_relat_1(X1) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(X1) = X0 ),
% 3.26/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_461,plain,
% 3.26/0.99      ( ~ v1_relat_1(X0)
% 3.26/0.99      | ~ v1_relat_1(X1)
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(X1)
% 3.26/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.26/0.99      | k2_relat_1(X0) != k1_relat_1(X1)
% 3.26/0.99      | k2_funct_1(X0) = X1
% 3.26/0.99      | sK2 != X0 ),
% 3.26/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_23]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_462,plain,
% 3.26/0.99      ( ~ v1_relat_1(X0)
% 3.26/0.99      | ~ v1_relat_1(sK2)
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_funct_1(sK2)
% 3.26/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0 ),
% 3.26/0.99      inference(unflattening,[status(thm)],[c_461]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_466,plain,
% 3.26/0.99      ( ~ v1_funct_1(X0)
% 3.26/0.99      | ~ v1_relat_1(sK2)
% 3.26/0.99      | ~ v1_relat_1(X0)
% 3.26/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_462,c_31]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_467,plain,
% 3.26/0.99      ( ~ v1_relat_1(X0)
% 3.26/0.99      | ~ v1_relat_1(sK2)
% 3.26/0.99      | ~ v1_funct_1(X0)
% 3.26/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0 ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_466]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1136,plain,
% 3.26/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_relat_1(sK2) != iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_468,plain,
% 3.26/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_relat_1(sK2) != iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1,plain,
% 3.26/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.26/0.99      | v1_relat_1(X0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f39]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1421,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.26/0.99      | v1_relat_1(sK2) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1422,plain,
% 3.26/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.26/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1421]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1572,plain,
% 3.26/0.99      ( v1_relat_1(X0) != iProver_top
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_1136,c_34,c_468,c_1422]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1573,plain,
% 3.26/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k2_relat_1(sK2) != k1_relat_1(X0)
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(renaming,[status(thm)],[c_1572]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1722,plain,
% 3.26/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.26/0.99      | k1_relat_1(X0) != sK1
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_1717,c_1573]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_3411,plain,
% 3.26/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 3.26/0.99      | k1_relat_1(X0) != sK1
% 3.26/0.99      | k2_funct_1(sK2) = X0
% 3.26/0.99      | v1_relat_1(X0) != iProver_top
% 3.26/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_3407,c_1722]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6775,plain,
% 3.26/0.99      ( k1_relat_1(sK3) != sK1
% 3.26/0.99      | k2_funct_1(sK2) = sK3
% 3.26/0.99      | v1_relat_1(sK3) != iProver_top
% 3.26/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_6699,c_3411]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2640,plain,
% 3.26/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.26/0.99      | sK0 = k1_xboole_0
% 3.26/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1148,c_1152]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2134,plain,
% 3.26/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.26/0.99      inference(superposition,[status(thm)],[c_1148,c_1159]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_2660,plain,
% 3.26/0.99      ( k1_relat_1(sK3) = sK1
% 3.26/0.99      | sK0 = k1_xboole_0
% 3.26/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.26/0.99      inference(demodulation,[status(thm)],[c_2640,c_2134]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_27,negated_conjecture,
% 3.26/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.26/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_36,plain,
% 3.26/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_22,negated_conjecture,
% 3.26/0.99      ( k1_xboole_0 != sK0 ),
% 3.26/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1450,plain,
% 3.26/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_697]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1451,plain,
% 3.26/0.99      ( sK0 != k1_xboole_0
% 3.26/0.99      | k1_xboole_0 = sK0
% 3.26/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1450]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_5905,plain,
% 3.26/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.26/0.99      inference(global_propositional_subsumption,
% 3.26/0.99                [status(thm)],
% 3.26/0.99                [c_2660,c_36,c_22,c_727,c_1451]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6780,plain,
% 3.26/0.99      ( k2_funct_1(sK2) = sK3
% 3.26/0.99      | sK1 != sK1
% 3.26/0.99      | v1_relat_1(sK3) != iProver_top
% 3.26/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.26/0.99      inference(light_normalisation,[status(thm)],[c_6775,c_5905]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_6781,plain,
% 3.26/0.99      ( k2_funct_1(sK2) = sK3
% 3.26/0.99      | v1_relat_1(sK3) != iProver_top
% 3.26/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.26/0.99      inference(equality_resolution_simp,[status(thm)],[c_6780]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1418,plain,
% 3.26/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.26/0.99      | v1_relat_1(sK3) ),
% 3.26/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_1419,plain,
% 3.26/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.26/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.26/0.99      inference(predicate_to_equality,[status(thm)],[c_1418]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(c_20,negated_conjecture,
% 3.26/0.99      ( k2_funct_1(sK2) != sK3 ),
% 3.26/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.26/0.99  
% 3.26/0.99  cnf(contradiction,plain,
% 3.26/0.99      ( $false ),
% 3.26/0.99      inference(minisat,[status(thm)],[c_6781,c_1419,c_20,c_37,c_35]) ).
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.26/0.99  
% 3.26/0.99  ------                               Statistics
% 3.26/0.99  
% 3.26/0.99  ------ General
% 3.26/0.99  
% 3.26/0.99  abstr_ref_over_cycles:                  0
% 3.26/0.99  abstr_ref_under_cycles:                 0
% 3.26/0.99  gc_basic_clause_elim:                   0
% 3.26/0.99  forced_gc_time:                         0
% 3.26/0.99  parsing_time:                           0.012
% 3.26/0.99  unif_index_cands_time:                  0.
% 3.26/0.99  unif_index_add_time:                    0.
% 3.26/0.99  orderings_time:                         0.
% 3.26/0.99  out_proof_time:                         0.013
% 3.26/0.99  total_time:                             0.248
% 3.26/0.99  num_of_symbols:                         52
% 3.26/0.99  num_of_terms:                           7457
% 3.26/0.99  
% 3.26/0.99  ------ Preprocessing
% 3.26/0.99  
% 3.26/0.99  num_of_splits:                          0
% 3.26/0.99  num_of_split_atoms:                     0
% 3.26/0.99  num_of_reused_defs:                     0
% 3.26/0.99  num_eq_ax_congr_red:                    9
% 3.26/0.99  num_of_sem_filtered_clauses:            1
% 3.26/0.99  num_of_subtypes:                        0
% 3.26/0.99  monotx_restored_types:                  0
% 3.26/0.99  sat_num_of_epr_types:                   0
% 3.26/0.99  sat_num_of_non_cyclic_types:            0
% 3.26/0.99  sat_guarded_non_collapsed_types:        0
% 3.26/0.99  num_pure_diseq_elim:                    0
% 3.26/0.99  simp_replaced_by:                       0
% 3.26/0.99  res_preprocessed:                       152
% 3.26/0.99  prep_upred:                             0
% 3.26/0.99  prep_unflattend:                        14
% 3.26/0.99  smt_new_axioms:                         0
% 3.26/0.99  pred_elim_cands:                        4
% 3.26/0.99  pred_elim:                              2
% 3.26/0.99  pred_elim_cl:                           3
% 3.26/0.99  pred_elim_cycles:                       4
% 3.26/0.99  merged_defs:                            0
% 3.26/0.99  merged_defs_ncl:                        0
% 3.26/0.99  bin_hyper_res:                          0
% 3.26/0.99  prep_cycles:                            4
% 3.26/0.99  pred_elim_time:                         0.006
% 3.26/0.99  splitting_time:                         0.
% 3.26/0.99  sem_filter_time:                        0.
% 3.26/0.99  monotx_time:                            0.
% 3.26/0.99  subtype_inf_time:                       0.
% 3.26/0.99  
% 3.26/0.99  ------ Problem properties
% 3.26/0.99  
% 3.26/0.99  clauses:                                29
% 3.26/0.99  conjectures:                            10
% 3.26/0.99  epr:                                    6
% 3.26/0.99  horn:                                   23
% 3.26/0.99  ground:                                 11
% 3.26/0.99  unary:                                  10
% 3.26/0.99  binary:                                 3
% 3.26/0.99  lits:                                   83
% 3.26/0.99  lits_eq:                                29
% 3.26/0.99  fd_pure:                                0
% 3.26/0.99  fd_pseudo:                              0
% 3.26/0.99  fd_cond:                                6
% 3.26/0.99  fd_pseudo_cond:                         0
% 3.26/0.99  ac_symbols:                             0
% 3.26/0.99  
% 3.26/0.99  ------ Propositional Solver
% 3.26/0.99  
% 3.26/0.99  prop_solver_calls:                      28
% 3.26/0.99  prop_fast_solver_calls:                 1203
% 3.26/0.99  smt_solver_calls:                       0
% 3.26/0.99  smt_fast_solver_calls:                  0
% 3.26/0.99  prop_num_of_clauses:                    2884
% 3.26/0.99  prop_preprocess_simplified:             8147
% 3.26/0.99  prop_fo_subsumed:                       56
% 3.26/0.99  prop_solver_time:                       0.
% 3.26/0.99  smt_solver_time:                        0.
% 3.26/0.99  smt_fast_solver_time:                   0.
% 3.26/0.99  prop_fast_solver_time:                  0.
% 3.26/0.99  prop_unsat_core_time:                   0.
% 3.26/0.99  
% 3.26/0.99  ------ QBF
% 3.26/0.99  
% 3.26/0.99  qbf_q_res:                              0
% 3.26/0.99  qbf_num_tautologies:                    0
% 3.26/0.99  qbf_prep_cycles:                        0
% 3.26/0.99  
% 3.26/0.99  ------ BMC1
% 3.26/0.99  
% 3.26/0.99  bmc1_current_bound:                     -1
% 3.26/0.99  bmc1_last_solved_bound:                 -1
% 3.26/0.99  bmc1_unsat_core_size:                   -1
% 3.26/0.99  bmc1_unsat_core_parents_size:           -1
% 3.26/0.99  bmc1_merge_next_fun:                    0
% 3.26/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.26/0.99  
% 3.26/0.99  ------ Instantiation
% 3.26/0.99  
% 3.26/0.99  inst_num_of_clauses:                    814
% 3.26/0.99  inst_num_in_passive:                    358
% 3.26/0.99  inst_num_in_active:                     400
% 3.26/0.99  inst_num_in_unprocessed:                56
% 3.26/0.99  inst_num_of_loops:                      410
% 3.26/0.99  inst_num_of_learning_restarts:          0
% 3.26/0.99  inst_num_moves_active_passive:          7
% 3.26/0.99  inst_lit_activity:                      0
% 3.26/0.99  inst_lit_activity_moves:                0
% 3.26/0.99  inst_num_tautologies:                   0
% 3.26/0.99  inst_num_prop_implied:                  0
% 3.26/0.99  inst_num_existing_simplified:           0
% 3.26/0.99  inst_num_eq_res_simplified:             0
% 3.26/0.99  inst_num_child_elim:                    0
% 3.26/0.99  inst_num_of_dismatching_blockings:      22
% 3.26/0.99  inst_num_of_non_proper_insts:           586
% 3.26/0.99  inst_num_of_duplicates:                 0
% 3.26/0.99  inst_inst_num_from_inst_to_res:         0
% 3.26/0.99  inst_dismatching_checking_time:         0.
% 3.26/0.99  
% 3.26/0.99  ------ Resolution
% 3.26/0.99  
% 3.26/0.99  res_num_of_clauses:                     0
% 3.26/0.99  res_num_in_passive:                     0
% 3.26/0.99  res_num_in_active:                      0
% 3.26/0.99  res_num_of_loops:                       156
% 3.26/0.99  res_forward_subset_subsumed:            57
% 3.26/0.99  res_backward_subset_subsumed:           0
% 3.26/0.99  res_forward_subsumed:                   0
% 3.26/0.99  res_backward_subsumed:                  0
% 3.26/0.99  res_forward_subsumption_resolution:     0
% 3.26/0.99  res_backward_subsumption_resolution:    0
% 3.26/0.99  res_clause_to_clause_subsumption:       173
% 3.26/0.99  res_orphan_elimination:                 0
% 3.26/0.99  res_tautology_del:                      29
% 3.26/0.99  res_num_eq_res_simplified:              0
% 3.26/0.99  res_num_sel_changes:                    0
% 3.26/0.99  res_moves_from_active_to_pass:          0
% 3.26/0.99  
% 3.26/0.99  ------ Superposition
% 3.26/0.99  
% 3.26/0.99  sup_time_total:                         0.
% 3.26/0.99  sup_time_generating:                    0.
% 3.26/0.99  sup_time_sim_full:                      0.
% 3.26/0.99  sup_time_sim_immed:                     0.
% 3.26/0.99  
% 3.26/0.99  sup_num_of_clauses:                     120
% 3.26/0.99  sup_num_in_active:                      72
% 3.26/0.99  sup_num_in_passive:                     48
% 3.26/0.99  sup_num_of_loops:                       80
% 3.26/0.99  sup_fw_superposition:                   35
% 3.26/0.99  sup_bw_superposition:                   64
% 3.26/0.99  sup_immediate_simplified:               15
% 3.26/0.99  sup_given_eliminated:                   0
% 3.26/0.99  comparisons_done:                       0
% 3.26/0.99  comparisons_avoided:                    0
% 3.26/0.99  
% 3.26/0.99  ------ Simplifications
% 3.26/0.99  
% 3.26/0.99  
% 3.26/0.99  sim_fw_subset_subsumed:                 6
% 3.26/0.99  sim_bw_subset_subsumed:                 1
% 3.26/0.99  sim_fw_subsumed:                        0
% 3.26/0.99  sim_bw_subsumed:                        0
% 3.26/0.99  sim_fw_subsumption_res:                 0
% 3.26/0.99  sim_bw_subsumption_res:                 0
% 3.26/0.99  sim_tautology_del:                      0
% 3.26/0.99  sim_eq_tautology_del:                   4
% 3.26/0.99  sim_eq_res_simp:                        1
% 3.26/0.99  sim_fw_demodulated:                     5
% 3.26/0.99  sim_bw_demodulated:                     9
% 3.26/0.99  sim_light_normalised:                   4
% 3.26/0.99  sim_joinable_taut:                      0
% 3.26/0.99  sim_joinable_simp:                      0
% 3.26/0.99  sim_ac_normalised:                      0
% 3.26/0.99  sim_smt_subsumption:                    0
% 3.26/0.99  
%------------------------------------------------------------------------------
