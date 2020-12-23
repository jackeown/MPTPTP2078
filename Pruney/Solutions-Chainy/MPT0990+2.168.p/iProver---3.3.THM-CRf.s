%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:32 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  202 (1183 expanded)
%              Number of clauses        :  136 ( 337 expanded)
%              Number of leaves         :   17 ( 309 expanded)
%              Depth                    :   24
%              Number of atoms          :  809 (10879 expanded)
%              Number of equality atoms :  394 (3907 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f65,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f63,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f64,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f71,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f60,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f73,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f48,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f10,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f44,f57])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f67,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f72,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f39])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f42,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1245,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1246,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3387,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1246])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_37,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3578,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3387,c_37])).

cnf(c_3579,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3578])).

cnf(c_3589,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_3579])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_2310,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_3354,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2310])).

cnf(c_3737,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3589,c_33,c_31,c_30,c_28,c_3354])).

cnf(c_7,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_26,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_339,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_26])).

cnf(c_340,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_1239,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_340])).

cnf(c_3740,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3737,c_1239])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_410,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_25])).

cnf(c_411,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_415,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_411,c_33])).

cnf(c_416,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_415])).

cnf(c_1492,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_416])).

cnf(c_1493,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1492])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_458,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_25])).

cnf(c_459,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_463,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_459,c_33])).

cnf(c_464,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_463])).

cnf(c_1518,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_464])).

cnf(c_1519,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1248,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3742,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3737,c_1248])).

cnf(c_1234,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_2204,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1234])).

cnf(c_2223,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2204,c_35,c_36,c_27,c_1519])).

cnf(c_3389,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_1246])).

cnf(c_4280,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3389,c_35,c_36,c_27,c_1493])).

cnf(c_4281,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4280])).

cnf(c_4291,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_4281])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_356,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_25])).

cnf(c_357,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_361,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_33])).

cnf(c_362,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1 ),
    inference(renaming,[status(thm)],[c_361])).

cnf(c_1238,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_362])).

cnf(c_2772,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_27,c_1238])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1495,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_362])).

cnf(c_1767,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1495])).

cnf(c_2936,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2772,c_32,c_31,c_27,c_23,c_1767])).

cnf(c_4299,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4291,c_2936])).

cnf(c_4402,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4299,c_34])).

cnf(c_4405,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4402,c_1248])).

cnf(c_6619,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3740,c_34,c_35,c_36,c_37,c_39,c_27,c_1493,c_1519,c_3742,c_4405])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1249,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2798,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1249])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1255,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1836,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1242,c_1255])).

cnf(c_2810,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2798,c_1836])).

cnf(c_763,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_794,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_763])).

cnf(c_764,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1561,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_1562,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_3326,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2810,c_35,c_23,c_794,c_1562])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_482,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X1) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_25])).

cnf(c_483,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_33])).

cnf(c_1233,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_3330,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3326,c_1233])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1529,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1953,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1954,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1953])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2239,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2240,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2239])).

cnf(c_7024,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_funct_1(sK2) = X0
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k5_relat_1(sK2,X0) != k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3330,c_36,c_1954,c_2240])).

cnf(c_7025,plain,
    ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
    | k1_relat_1(X0) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = X0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7024])).

cnf(c_7036,plain,
    ( k1_relat_1(sK3) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6619,c_7025])).

cnf(c_2797,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1245,c_1249])).

cnf(c_1835,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1245,c_1255])).

cnf(c_2817,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2797,c_1835])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_38,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1563,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_764])).

cnf(c_1564,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1563])).

cnf(c_6019,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2817,c_38,c_24,c_794,c_1564])).

cnf(c_7041,plain,
    ( k2_relat_1(sK2) != sK1
    | k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7036,c_6019])).

cnf(c_2799,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2223,c_1249])).

cnf(c_2228,plain,
    ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2223,c_1255])).

cnf(c_2803,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2799,c_2228])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_435,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_439,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_435,c_33])).

cnf(c_440,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_439])).

cnf(c_1515,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_440])).

cnf(c_1516,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1515])).

cnf(c_4430,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2803,c_35,c_36,c_27,c_24,c_794,c_1516,c_1564])).

cnf(c_1257,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2273,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1257])).

cnf(c_2435,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2273,c_36,c_1954,c_2240])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_512,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_25])).

cnf(c_513,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_515,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_33])).

cnf(c_1232,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_515])).

cnf(c_2440,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2435,c_1232])).

cnf(c_4433,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_4430,c_2440])).

cnf(c_2236,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2237,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2236])).

cnf(c_1950,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1529])).

cnf(c_1951,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1950])).

cnf(c_22,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f74])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7041,c_4433,c_2237,c_1951,c_22,c_39,c_37])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.14/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/0.99  
% 3.14/0.99  ------  iProver source info
% 3.14/0.99  
% 3.14/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.14/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/0.99  git: non_committed_changes: false
% 3.14/0.99  git: last_make_outside_of_git: false
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     num_symb
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       true
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  ------ Parsing...
% 3.14/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/0.99  ------ Proving...
% 3.14/0.99  ------ Problem Properties 
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  clauses                                 31
% 3.14/0.99  conjectures                             10
% 3.14/0.99  EPR                                     6
% 3.14/0.99  Horn                                    25
% 3.14/0.99  unary                                   11
% 3.14/0.99  binary                                  3
% 3.14/0.99  lits                                    87
% 3.14/0.99  lits eq                                 30
% 3.14/0.99  fd_pure                                 0
% 3.14/0.99  fd_pseudo                               0
% 3.14/0.99  fd_cond                                 6
% 3.14/0.99  fd_pseudo_cond                          0
% 3.14/0.99  AC symbols                              0
% 3.14/0.99  
% 3.14/0.99  ------ Schedule dynamic 5 is on 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ 
% 3.14/0.99  Current options:
% 3.14/0.99  ------ 
% 3.14/0.99  
% 3.14/0.99  ------ Input Options
% 3.14/0.99  
% 3.14/0.99  --out_options                           all
% 3.14/0.99  --tptp_safe_out                         true
% 3.14/0.99  --problem_path                          ""
% 3.14/0.99  --include_path                          ""
% 3.14/0.99  --clausifier                            res/vclausify_rel
% 3.14/0.99  --clausifier_options                    --mode clausify
% 3.14/0.99  --stdin                                 false
% 3.14/0.99  --stats_out                             all
% 3.14/0.99  
% 3.14/0.99  ------ General Options
% 3.14/0.99  
% 3.14/0.99  --fof                                   false
% 3.14/0.99  --time_out_real                         305.
% 3.14/0.99  --time_out_virtual                      -1.
% 3.14/0.99  --symbol_type_check                     false
% 3.14/0.99  --clausify_out                          false
% 3.14/0.99  --sig_cnt_out                           false
% 3.14/0.99  --trig_cnt_out                          false
% 3.14/0.99  --trig_cnt_out_tolerance                1.
% 3.14/0.99  --trig_cnt_out_sk_spl                   false
% 3.14/0.99  --abstr_cl_out                          false
% 3.14/0.99  
% 3.14/0.99  ------ Global Options
% 3.14/0.99  
% 3.14/0.99  --schedule                              default
% 3.14/0.99  --add_important_lit                     false
% 3.14/0.99  --prop_solver_per_cl                    1000
% 3.14/0.99  --min_unsat_core                        false
% 3.14/0.99  --soft_assumptions                      false
% 3.14/0.99  --soft_lemma_size                       3
% 3.14/0.99  --prop_impl_unit_size                   0
% 3.14/0.99  --prop_impl_unit                        []
% 3.14/0.99  --share_sel_clauses                     true
% 3.14/0.99  --reset_solvers                         false
% 3.14/0.99  --bc_imp_inh                            [conj_cone]
% 3.14/0.99  --conj_cone_tolerance                   3.
% 3.14/0.99  --extra_neg_conj                        none
% 3.14/0.99  --large_theory_mode                     true
% 3.14/0.99  --prolific_symb_bound                   200
% 3.14/0.99  --lt_threshold                          2000
% 3.14/0.99  --clause_weak_htbl                      true
% 3.14/0.99  --gc_record_bc_elim                     false
% 3.14/0.99  
% 3.14/0.99  ------ Preprocessing Options
% 3.14/0.99  
% 3.14/0.99  --preprocessing_flag                    true
% 3.14/0.99  --time_out_prep_mult                    0.1
% 3.14/0.99  --splitting_mode                        input
% 3.14/0.99  --splitting_grd                         true
% 3.14/0.99  --splitting_cvd                         false
% 3.14/0.99  --splitting_cvd_svl                     false
% 3.14/0.99  --splitting_nvd                         32
% 3.14/0.99  --sub_typing                            true
% 3.14/0.99  --prep_gs_sim                           true
% 3.14/0.99  --prep_unflatten                        true
% 3.14/0.99  --prep_res_sim                          true
% 3.14/0.99  --prep_upred                            true
% 3.14/0.99  --prep_sem_filter                       exhaustive
% 3.14/0.99  --prep_sem_filter_out                   false
% 3.14/0.99  --pred_elim                             true
% 3.14/0.99  --res_sim_input                         true
% 3.14/0.99  --eq_ax_congr_red                       true
% 3.14/0.99  --pure_diseq_elim                       true
% 3.14/0.99  --brand_transform                       false
% 3.14/0.99  --non_eq_to_eq                          false
% 3.14/0.99  --prep_def_merge                        true
% 3.14/0.99  --prep_def_merge_prop_impl              false
% 3.14/0.99  --prep_def_merge_mbd                    true
% 3.14/0.99  --prep_def_merge_tr_red                 false
% 3.14/0.99  --prep_def_merge_tr_cl                  false
% 3.14/0.99  --smt_preprocessing                     true
% 3.14/0.99  --smt_ac_axioms                         fast
% 3.14/0.99  --preprocessed_out                      false
% 3.14/0.99  --preprocessed_stats                    false
% 3.14/0.99  
% 3.14/0.99  ------ Abstraction refinement Options
% 3.14/0.99  
% 3.14/0.99  --abstr_ref                             []
% 3.14/0.99  --abstr_ref_prep                        false
% 3.14/0.99  --abstr_ref_until_sat                   false
% 3.14/0.99  --abstr_ref_sig_restrict                funpre
% 3.14/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.14/0.99  --abstr_ref_under                       []
% 3.14/0.99  
% 3.14/0.99  ------ SAT Options
% 3.14/0.99  
% 3.14/0.99  --sat_mode                              false
% 3.14/0.99  --sat_fm_restart_options                ""
% 3.14/0.99  --sat_gr_def                            false
% 3.14/0.99  --sat_epr_types                         true
% 3.14/0.99  --sat_non_cyclic_types                  false
% 3.14/0.99  --sat_finite_models                     false
% 3.14/0.99  --sat_fm_lemmas                         false
% 3.14/0.99  --sat_fm_prep                           false
% 3.14/0.99  --sat_fm_uc_incr                        true
% 3.14/0.99  --sat_out_model                         small
% 3.14/0.99  --sat_out_clauses                       false
% 3.14/0.99  
% 3.14/0.99  ------ QBF Options
% 3.14/0.99  
% 3.14/0.99  --qbf_mode                              false
% 3.14/0.99  --qbf_elim_univ                         false
% 3.14/0.99  --qbf_dom_inst                          none
% 3.14/0.99  --qbf_dom_pre_inst                      false
% 3.14/0.99  --qbf_sk_in                             false
% 3.14/0.99  --qbf_pred_elim                         true
% 3.14/0.99  --qbf_split                             512
% 3.14/0.99  
% 3.14/0.99  ------ BMC1 Options
% 3.14/0.99  
% 3.14/0.99  --bmc1_incremental                      false
% 3.14/0.99  --bmc1_axioms                           reachable_all
% 3.14/0.99  --bmc1_min_bound                        0
% 3.14/0.99  --bmc1_max_bound                        -1
% 3.14/0.99  --bmc1_max_bound_default                -1
% 3.14/0.99  --bmc1_symbol_reachability              true
% 3.14/0.99  --bmc1_property_lemmas                  false
% 3.14/0.99  --bmc1_k_induction                      false
% 3.14/0.99  --bmc1_non_equiv_states                 false
% 3.14/0.99  --bmc1_deadlock                         false
% 3.14/0.99  --bmc1_ucm                              false
% 3.14/0.99  --bmc1_add_unsat_core                   none
% 3.14/0.99  --bmc1_unsat_core_children              false
% 3.14/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.14/0.99  --bmc1_out_stat                         full
% 3.14/0.99  --bmc1_ground_init                      false
% 3.14/0.99  --bmc1_pre_inst_next_state              false
% 3.14/0.99  --bmc1_pre_inst_state                   false
% 3.14/0.99  --bmc1_pre_inst_reach_state             false
% 3.14/0.99  --bmc1_out_unsat_core                   false
% 3.14/0.99  --bmc1_aig_witness_out                  false
% 3.14/0.99  --bmc1_verbose                          false
% 3.14/0.99  --bmc1_dump_clauses_tptp                false
% 3.14/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.14/0.99  --bmc1_dump_file                        -
% 3.14/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.14/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.14/0.99  --bmc1_ucm_extend_mode                  1
% 3.14/0.99  --bmc1_ucm_init_mode                    2
% 3.14/0.99  --bmc1_ucm_cone_mode                    none
% 3.14/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.14/0.99  --bmc1_ucm_relax_model                  4
% 3.14/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.14/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.14/0.99  --bmc1_ucm_layered_model                none
% 3.14/0.99  --bmc1_ucm_max_lemma_size               10
% 3.14/0.99  
% 3.14/0.99  ------ AIG Options
% 3.14/0.99  
% 3.14/0.99  --aig_mode                              false
% 3.14/0.99  
% 3.14/0.99  ------ Instantiation Options
% 3.14/0.99  
% 3.14/0.99  --instantiation_flag                    true
% 3.14/0.99  --inst_sos_flag                         false
% 3.14/0.99  --inst_sos_phase                        true
% 3.14/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.14/0.99  --inst_lit_sel_side                     none
% 3.14/0.99  --inst_solver_per_active                1400
% 3.14/0.99  --inst_solver_calls_frac                1.
% 3.14/0.99  --inst_passive_queue_type               priority_queues
% 3.14/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.14/0.99  --inst_passive_queues_freq              [25;2]
% 3.14/0.99  --inst_dismatching                      true
% 3.14/0.99  --inst_eager_unprocessed_to_passive     true
% 3.14/0.99  --inst_prop_sim_given                   true
% 3.14/0.99  --inst_prop_sim_new                     false
% 3.14/0.99  --inst_subs_new                         false
% 3.14/0.99  --inst_eq_res_simp                      false
% 3.14/0.99  --inst_subs_given                       false
% 3.14/0.99  --inst_orphan_elimination               true
% 3.14/0.99  --inst_learning_loop_flag               true
% 3.14/0.99  --inst_learning_start                   3000
% 3.14/0.99  --inst_learning_factor                  2
% 3.14/0.99  --inst_start_prop_sim_after_learn       3
% 3.14/0.99  --inst_sel_renew                        solver
% 3.14/0.99  --inst_lit_activity_flag                true
% 3.14/0.99  --inst_restr_to_given                   false
% 3.14/0.99  --inst_activity_threshold               500
% 3.14/0.99  --inst_out_proof                        true
% 3.14/0.99  
% 3.14/0.99  ------ Resolution Options
% 3.14/0.99  
% 3.14/0.99  --resolution_flag                       false
% 3.14/0.99  --res_lit_sel                           adaptive
% 3.14/0.99  --res_lit_sel_side                      none
% 3.14/0.99  --res_ordering                          kbo
% 3.14/0.99  --res_to_prop_solver                    active
% 3.14/0.99  --res_prop_simpl_new                    false
% 3.14/0.99  --res_prop_simpl_given                  true
% 3.14/0.99  --res_passive_queue_type                priority_queues
% 3.14/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.14/0.99  --res_passive_queues_freq               [15;5]
% 3.14/0.99  --res_forward_subs                      full
% 3.14/0.99  --res_backward_subs                     full
% 3.14/0.99  --res_forward_subs_resolution           true
% 3.14/0.99  --res_backward_subs_resolution          true
% 3.14/0.99  --res_orphan_elimination                true
% 3.14/0.99  --res_time_limit                        2.
% 3.14/0.99  --res_out_proof                         true
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Options
% 3.14/0.99  
% 3.14/0.99  --superposition_flag                    true
% 3.14/0.99  --sup_passive_queue_type                priority_queues
% 3.14/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.14/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.14/0.99  --demod_completeness_check              fast
% 3.14/0.99  --demod_use_ground                      true
% 3.14/0.99  --sup_to_prop_solver                    passive
% 3.14/0.99  --sup_prop_simpl_new                    true
% 3.14/0.99  --sup_prop_simpl_given                  true
% 3.14/0.99  --sup_fun_splitting                     false
% 3.14/0.99  --sup_smt_interval                      50000
% 3.14/0.99  
% 3.14/0.99  ------ Superposition Simplification Setup
% 3.14/0.99  
% 3.14/0.99  --sup_indices_passive                   []
% 3.14/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.14/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.14/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_full_bw                           [BwDemod]
% 3.14/0.99  --sup_immed_triv                        [TrivRules]
% 3.14/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.14/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_immed_bw_main                     []
% 3.14/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.14/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.14/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.14/0.99  
% 3.14/0.99  ------ Combination Options
% 3.14/0.99  
% 3.14/0.99  --comb_res_mult                         3
% 3.14/0.99  --comb_sup_mult                         2
% 3.14/0.99  --comb_inst_mult                        10
% 3.14/0.99  
% 3.14/0.99  ------ Debug Options
% 3.14/0.99  
% 3.14/0.99  --dbg_backtrace                         false
% 3.14/0.99  --dbg_dump_prop_clauses                 false
% 3.14/0.99  --dbg_dump_prop_clauses_file            -
% 3.14/0.99  --dbg_out_stat                          false
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  ------ Proving...
% 3.14/0.99  
% 3.14/0.99  
% 3.14/0.99  % SZS status Theorem for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/0.99  
% 3.14/0.99  fof(f13,conjecture,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f14,negated_conjecture,(
% 3.14/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.14/0.99    inference(negated_conjecture,[],[f13])).
% 3.14/0.99  
% 3.14/0.99  fof(f33,plain,(
% 3.14/0.99    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.14/0.99    inference(ennf_transformation,[],[f14])).
% 3.14/0.99  
% 3.14/0.99  fof(f34,plain,(
% 3.14/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.14/0.99    inference(flattening,[],[f33])).
% 3.14/0.99  
% 3.14/0.99  fof(f38,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f37,plain,(
% 3.14/0.99    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.14/0.99    introduced(choice_axiom,[])).
% 3.14/0.99  
% 3.14/0.99  fof(f39,plain,(
% 3.14/0.99    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.14/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f38,f37])).
% 3.14/0.99  
% 3.14/0.99  fof(f65,plain,(
% 3.14/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f68,plain,(
% 3.14/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f9,axiom,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f27,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.14/0.99    inference(ennf_transformation,[],[f9])).
% 3.14/0.99  
% 3.14/0.99  fof(f28,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.14/0.99    inference(flattening,[],[f27])).
% 3.14/0.99  
% 3.14/0.99  fof(f56,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f28])).
% 3.14/0.99  
% 3.14/0.99  fof(f66,plain,(
% 3.14/0.99    v1_funct_1(sK3)),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f63,plain,(
% 3.14/0.99    v1_funct_1(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f6,axiom,(
% 3.14/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f21,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.14/0.99    inference(ennf_transformation,[],[f6])).
% 3.14/0.99  
% 3.14/0.99  fof(f22,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(flattening,[],[f21])).
% 3.14/0.99  
% 3.14/0.99  fof(f35,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(nnf_transformation,[],[f22])).
% 3.14/0.99  
% 3.14/0.99  fof(f46,plain,(
% 3.14/0.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f35])).
% 3.14/0.99  
% 3.14/0.99  fof(f70,plain,(
% 3.14/0.99    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f64,plain,(
% 3.14/0.99    v1_funct_2(sK2,sK0,sK1)),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f69,plain,(
% 3.14/0.99    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f11,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f29,plain,(
% 3.14/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.14/0.99    inference(ennf_transformation,[],[f11])).
% 3.14/0.99  
% 3.14/0.99  fof(f30,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.14/0.99    inference(flattening,[],[f29])).
% 3.14/0.99  
% 3.14/0.99  fof(f58,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f71,plain,(
% 3.14/0.99    v2_funct_1(sK2)),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f60,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f8,axiom,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f25,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.14/0.99    inference(ennf_transformation,[],[f8])).
% 3.14/0.99  
% 3.14/0.99  fof(f26,plain,(
% 3.14/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.14/0.99    inference(flattening,[],[f25])).
% 3.14/0.99  
% 3.14/0.99  fof(f55,plain,(
% 3.14/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f26])).
% 3.14/0.99  
% 3.14/0.99  fof(f12,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f31,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.14/0.99    inference(ennf_transformation,[],[f12])).
% 3.14/0.99  
% 3.14/0.99  fof(f32,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.14/0.99    inference(flattening,[],[f31])).
% 3.14/0.99  
% 3.14/0.99  fof(f61,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f32])).
% 3.14/0.99  
% 3.14/0.99  fof(f73,plain,(
% 3.14/0.99    k1_xboole_0 != sK1),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f7,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f23,plain,(
% 3.14/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(ennf_transformation,[],[f7])).
% 3.14/0.99  
% 3.14/0.99  fof(f24,plain,(
% 3.14/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(flattening,[],[f23])).
% 3.14/0.99  
% 3.14/0.99  fof(f36,plain,(
% 3.14/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(nnf_transformation,[],[f24])).
% 3.14/0.99  
% 3.14/0.99  fof(f48,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f36])).
% 3.14/0.99  
% 3.14/0.99  fof(f5,axiom,(
% 3.14/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f20,plain,(
% 3.14/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/0.99    inference(ennf_transformation,[],[f5])).
% 3.14/0.99  
% 3.14/0.99  fof(f45,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f20])).
% 3.14/0.99  
% 3.14/0.99  fof(f4,axiom,(
% 3.14/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f18,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f4])).
% 3.14/0.99  
% 3.14/0.99  fof(f19,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.99    inference(flattening,[],[f18])).
% 3.14/0.99  
% 3.14/0.99  fof(f44,plain,(
% 3.14/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f19])).
% 3.14/0.99  
% 3.14/0.99  fof(f10,axiom,(
% 3.14/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f57,plain,(
% 3.14/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f10])).
% 3.14/0.99  
% 3.14/0.99  fof(f75,plain,(
% 3.14/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.99    inference(definition_unfolding,[],[f44,f57])).
% 3.14/0.99  
% 3.14/0.99  fof(f1,axiom,(
% 3.14/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f15,plain,(
% 3.14/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.14/0.99    inference(ennf_transformation,[],[f1])).
% 3.14/0.99  
% 3.14/0.99  fof(f40,plain,(
% 3.14/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f15])).
% 3.14/0.99  
% 3.14/0.99  fof(f2,axiom,(
% 3.14/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f41,plain,(
% 3.14/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.14/0.99    inference(cnf_transformation,[],[f2])).
% 3.14/0.99  
% 3.14/0.99  fof(f67,plain,(
% 3.14/0.99    v1_funct_2(sK3,sK1,sK0)),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f72,plain,(
% 3.14/0.99    k1_xboole_0 != sK0),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  fof(f59,plain,(
% 3.14/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f30])).
% 3.14/0.99  
% 3.14/0.99  fof(f3,axiom,(
% 3.14/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.14/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.14/0.99  
% 3.14/0.99  fof(f16,plain,(
% 3.14/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/0.99    inference(ennf_transformation,[],[f3])).
% 3.14/0.99  
% 3.14/0.99  fof(f17,plain,(
% 3.14/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/0.99    inference(flattening,[],[f16])).
% 3.14/0.99  
% 3.14/0.99  fof(f42,plain,(
% 3.14/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/0.99    inference(cnf_transformation,[],[f17])).
% 3.14/0.99  
% 3.14/0.99  fof(f74,plain,(
% 3.14/0.99    k2_funct_1(sK2) != sK3),
% 3.14/0.99    inference(cnf_transformation,[],[f39])).
% 3.14/0.99  
% 3.14/0.99  cnf(c_31,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1242,plain,
% 3.14/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_28,negated_conjecture,
% 3.14/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.14/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1245,plain,
% 3.14/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_16,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(X3)
% 3.14/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1246,plain,
% 3.14/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.14/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.14/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | v1_funct_1(X5) != iProver_top
% 3.14/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3387,plain,
% 3.14/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | v1_funct_1(X2) != iProver_top
% 3.14/0.99      | v1_funct_1(sK3) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1245,c_1246]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_30,negated_conjecture,
% 3.14/0.99      ( v1_funct_1(sK3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_37,plain,
% 3.14/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3578,plain,
% 3.14/0.99      ( v1_funct_1(X2) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3387,c_37]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3579,plain,
% 3.14/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_3578]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3589,plain,
% 3.14/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.14/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1242,c_3579]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_33,negated_conjecture,
% 3.14/0.99      ( v1_funct_1(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1631,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(sK3)
% 3.14/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1891,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.14/0.99      | ~ v1_funct_1(sK3)
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1631]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2310,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ v1_funct_1(sK3)
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1891]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3354,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | ~ v1_funct_1(sK3)
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_2310]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3737,plain,
% 3.14/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3589,c_33,c_31,c_30,c_28,c_3354]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7,plain,
% 3.14/0.99      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.14/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | X3 = X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_26,negated_conjecture,
% 3.14/0.99      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_339,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | X3 = X0
% 3.14/0.99      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.14/0.99      | k6_partfun1(sK0) != X3
% 3.14/0.99      | sK0 != X2
% 3.14/0.99      | sK0 != X1 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_26]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_340,plain,
% 3.14/0.99      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.14/0.99      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.14/0.99      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_339]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1239,plain,
% 3.14/0.99      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.14/0.99      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.14/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_340]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3740,plain,
% 3.14/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.14/0.99      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 3.14/0.99      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_3737,c_1239]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_34,plain,
% 3.14/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_32,negated_conjecture,
% 3.14/0.99      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.14/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_35,plain,
% 3.14/0.99      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_36,plain,
% 3.14/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_39,plain,
% 3.14/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_27,negated_conjecture,
% 3.14/0.99      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.14/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_19,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.14/0.99      | ~ v2_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_25,negated_conjecture,
% 3.14/0.99      ( v2_funct_1(sK2) ),
% 3.14/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_410,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_411,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_410]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_415,plain,
% 3.14/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_411,c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_416,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_415]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1492,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.14/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_416]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1493,plain,
% 3.14/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1492]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_17,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v2_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_458,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_459,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_458]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_463,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_459,c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_464,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_463]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1518,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_464]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1519,plain,
% 3.14/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_14,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.14/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(X3) ),
% 3.14/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1248,plain,
% 3.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.14/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.14/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.14/0.99      | v1_funct_1(X0) != iProver_top
% 3.14/0.99      | v1_funct_1(X3) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3742,plain,
% 3.14/0.99      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.14/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.14/0.99      | v1_funct_1(sK3) != iProver_top
% 3.14/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_3737,c_1248]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1234,plain,
% 3.14/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.14/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2204,plain,
% 3.14/0.99      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_27,c_1234]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2223,plain,
% 3.14/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2204,c_35,c_36,c_27,c_1519]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3389,plain,
% 3.14/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | v1_funct_1(X2) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2223,c_1246]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4280,plain,
% 3.14/0.99      ( v1_funct_1(X2) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3389,c_35,c_36,c_27,c_1493]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4281,plain,
% 3.14/0.99      ( k1_partfun1(X0,X1,sK1,sK0,X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.14/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_4280]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4291,plain,
% 3.14/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
% 3.14/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1242,c_4281]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_21,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v2_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.14/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.14/0.99      | k1_xboole_0 = X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_356,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.14/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.14/0.99      | sK2 != X0
% 3.14/0.99      | k1_xboole_0 = X2 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_357,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.14/0.99      | k1_xboole_0 = X1 ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_361,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.14/0.99      | k1_xboole_0 = X1 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_357,c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_362,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.14/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.14/0.99      | k1_xboole_0 = X1 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_361]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1238,plain,
% 3.14/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.14/0.99      | k1_xboole_0 = X1
% 3.14/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_362]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2772,plain,
% 3.14/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.14/0.99      | sK1 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_27,c_1238]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_23,negated_conjecture,
% 3.14/0.99      ( k1_xboole_0 != sK1 ),
% 3.14/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1495,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.14/0.99      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.14/0.99      | k1_xboole_0 = sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_362]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1767,plain,
% 3.14/0.99      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.14/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.14/0.99      | k1_xboole_0 = sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1495]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2936,plain,
% 3.14/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2772,c_32,c_31,c_27,c_23,c_1767]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4299,plain,
% 3.14/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.14/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_4291,c_2936]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4402,plain,
% 3.14/0.99      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_4299,c_34]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4405,plain,
% 3.14/0.99      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 3.14/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.14/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.14/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_4402,c_1248]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6619,plain,
% 3.14/0.99      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3740,c_34,c_35,c_36,c_37,c_39,c_27,c_1493,c_1519,
% 3.14/0.99                 c_3742,c_4405]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_13,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.14/0.99      | k1_xboole_0 = X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1249,plain,
% 3.14/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.14/0.99      | k1_xboole_0 = X1
% 3.14/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2798,plain,
% 3.14/0.99      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 3.14/0.99      | sK1 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1242,c_1249]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_5,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1255,plain,
% 3.14/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1836,plain,
% 3.14/0.99      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1242,c_1255]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2810,plain,
% 3.14/0.99      ( k1_relat_1(sK2) = sK0
% 3.14/0.99      | sK1 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_2798,c_1836]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_763,plain,( X0 = X0 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_794,plain,
% 3.14/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_763]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_764,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1561,plain,
% 3.14/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_764]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1562,plain,
% 3.14/0.99      ( sK1 != k1_xboole_0
% 3.14/0.99      | k1_xboole_0 = sK1
% 3.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1561]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3326,plain,
% 3.14/0.99      ( k1_relat_1(sK2) = sK0 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2810,c_35,c_23,c_794,c_1562]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4,plain,
% 3.14/0.99      ( ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(X1)
% 3.14/0.99      | ~ v2_funct_1(X0)
% 3.14/0.99      | ~ v1_relat_1(X0)
% 3.14/0.99      | ~ v1_relat_1(X1)
% 3.14/0.99      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.14/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.14/0.99      | k2_funct_1(X0) = X1 ),
% 3.14/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_482,plain,
% 3.14/0.99      ( ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(X1)
% 3.14/0.99      | ~ v1_relat_1(X0)
% 3.14/0.99      | ~ v1_relat_1(X1)
% 3.14/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k1_relat_1(X1))
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(X1)
% 3.14/0.99      | k2_funct_1(X1) = X0
% 3.14/0.99      | sK2 != X1 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_483,plain,
% 3.14/0.99      ( ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | ~ v1_relat_1(X0)
% 3.14/0.99      | ~ v1_relat_1(sK2)
% 3.14/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = X0 ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_487,plain,
% 3.14/0.99      ( ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v1_relat_1(X0)
% 3.14/0.99      | ~ v1_relat_1(sK2)
% 3.14/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = X0 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_483,c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1233,plain,
% 3.14/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(k1_relat_1(sK2))
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = X0
% 3.14/0.99      | v1_funct_1(X0) != iProver_top
% 3.14/0.99      | v1_relat_1(X0) != iProver_top
% 3.14/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_3330,plain,
% 3.14/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = X0
% 3.14/0.99      | v1_funct_1(X0) != iProver_top
% 3.14/0.99      | v1_relat_1(X0) != iProver_top
% 3.14/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_3326,c_1233]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_0,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.14/0.99      | ~ v1_relat_1(X1)
% 3.14/0.99      | v1_relat_1(X0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f40]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1529,plain,
% 3.14/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | v1_relat_1(X0)
% 3.14/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1953,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 3.14/0.99      | v1_relat_1(sK2) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1529]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1954,plain,
% 3.14/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.14/0.99      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.14/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1953]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1,plain,
% 3.14/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.14/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2239,plain,
% 3.14/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2240,plain,
% 3.14/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_2239]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7024,plain,
% 3.14/0.99      ( v1_relat_1(X0) != iProver_top
% 3.14/0.99      | v1_funct_1(X0) != iProver_top
% 3.14/0.99      | k2_funct_1(sK2) = X0
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k5_relat_1(sK2,X0) != k6_partfun1(sK0) ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_3330,c_36,c_1954,c_2240]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7025,plain,
% 3.14/0.99      ( k5_relat_1(sK2,X0) != k6_partfun1(sK0)
% 3.14/0.99      | k1_relat_1(X0) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = X0
% 3.14/0.99      | v1_funct_1(X0) != iProver_top
% 3.14/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_7024]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7036,plain,
% 3.14/0.99      ( k1_relat_1(sK3) != k2_relat_1(sK2)
% 3.14/0.99      | k2_funct_1(sK2) = sK3
% 3.14/0.99      | v1_funct_1(sK3) != iProver_top
% 3.14/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_6619,c_7025]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2797,plain,
% 3.14/0.99      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 3.14/0.99      | sK0 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1245,c_1249]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1835,plain,
% 3.14/0.99      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1245,c_1255]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2817,plain,
% 3.14/0.99      ( k1_relat_1(sK3) = sK1
% 3.14/0.99      | sK0 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_2797,c_1835]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_29,negated_conjecture,
% 3.14/0.99      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.14/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_38,plain,
% 3.14/0.99      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_24,negated_conjecture,
% 3.14/0.99      ( k1_xboole_0 != sK0 ),
% 3.14/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1563,plain,
% 3.14/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_764]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1564,plain,
% 3.14/0.99      ( sK0 != k1_xboole_0
% 3.14/0.99      | k1_xboole_0 = sK0
% 3.14/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_1563]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_6019,plain,
% 3.14/0.99      ( k1_relat_1(sK3) = sK1 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2817,c_38,c_24,c_794,c_1564]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_7041,plain,
% 3.14/0.99      ( k2_relat_1(sK2) != sK1
% 3.14/0.99      | k2_funct_1(sK2) = sK3
% 3.14/0.99      | v1_funct_1(sK3) != iProver_top
% 3.14/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.14/0.99      inference(light_normalisation,[status(thm)],[c_7036,c_6019]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2799,plain,
% 3.14/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = sK1
% 3.14/0.99      | sK0 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2223,c_1249]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2228,plain,
% 3.14/0.99      ( k1_relset_1(sK1,sK0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_2223,c_1255]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2803,plain,
% 3.14/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1
% 3.14/0.99      | sK0 = k1_xboole_0
% 3.14/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) != iProver_top ),
% 3.14/0.99      inference(demodulation,[status(thm)],[c_2799,c_2228]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_18,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | ~ v2_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.14/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_434,plain,
% 3.14/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.14/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/0.99      | ~ v1_funct_1(X0)
% 3.14/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.14/0.99      | sK2 != X0 ),
% 3.14/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_435,plain,
% 3.14/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.14/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | ~ v1_funct_1(sK2)
% 3.14/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.14/0.99      inference(unflattening,[status(thm)],[c_434]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_439,plain,
% 3.14/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.14/0.99      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.14/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_435,c_33]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_440,plain,
% 3.14/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.14/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.14/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.14/0.99      inference(renaming,[status(thm)],[c_439]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1515,plain,
% 3.14/0.99      ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.14/0.99      | ~ v1_funct_2(sK2,sK0,sK1)
% 3.14/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.14/0.99      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 3.14/0.99      inference(instantiation,[status(thm)],[c_440]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1516,plain,
% 3.14/0.99      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 3.14/0.99      | v1_funct_2(k2_funct_1(sK2),sK1,sK0) = iProver_top
% 3.14/0.99      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.14/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_1515]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_4430,plain,
% 3.14/0.99      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 3.14/0.99      inference(global_propositional_subsumption,
% 3.14/0.99                [status(thm)],
% 3.14/0.99                [c_2803,c_35,c_36,c_27,c_24,c_794,c_1516,c_1564]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_1257,plain,
% 3.14/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.14/0.99      | v1_relat_1(X1) != iProver_top
% 3.14/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.14/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.14/0.99  
% 3.14/0.99  cnf(c_2273,plain,
% 3.14/0.99      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.14/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.14/0.99      inference(superposition,[status(thm)],[c_1242,c_1257]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2435,plain,
% 3.14/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_2273,c_36,c_1954,c_2240]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_3,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v2_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.14/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_512,plain,
% 3.14/1.00      ( ~ v1_funct_1(X0)
% 3.14/1.00      | ~ v1_relat_1(X0)
% 3.14/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.14/1.00      | sK2 != X0 ),
% 3.14/1.00      inference(resolution_lifted,[status(thm)],[c_3,c_25]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_513,plain,
% 3.14/1.00      ( ~ v1_funct_1(sK2)
% 3.14/1.00      | ~ v1_relat_1(sK2)
% 3.14/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.14/1.00      inference(unflattening,[status(thm)],[c_512]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_515,plain,
% 3.14/1.00      ( ~ v1_relat_1(sK2)
% 3.14/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.14/1.00      inference(global_propositional_subsumption,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_513,c_33]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1232,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.14/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_515]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2440,plain,
% 3.14/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.14/1.00      inference(superposition,[status(thm)],[c_2435,c_1232]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_4433,plain,
% 3.14/1.00      ( k2_relat_1(sK2) = sK1 ),
% 3.14/1.00      inference(demodulation,[status(thm)],[c_4430,c_2440]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2236,plain,
% 3.14/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_2237,plain,
% 3.14/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_2236]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1950,plain,
% 3.14/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.14/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 3.14/1.00      | v1_relat_1(sK3) ),
% 3.14/1.00      inference(instantiation,[status(thm)],[c_1529]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_1951,plain,
% 3.14/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.14/1.00      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.14/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.14/1.00      inference(predicate_to_equality,[status(thm)],[c_1950]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(c_22,negated_conjecture,
% 3.14/1.00      ( k2_funct_1(sK2) != sK3 ),
% 3.14/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.14/1.00  
% 3.14/1.00  cnf(contradiction,plain,
% 3.14/1.00      ( $false ),
% 3.14/1.00      inference(minisat,
% 3.14/1.00                [status(thm)],
% 3.14/1.00                [c_7041,c_4433,c_2237,c_1951,c_22,c_39,c_37]) ).
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.00  
% 3.14/1.00  ------                               Statistics
% 3.14/1.00  
% 3.14/1.00  ------ General
% 3.14/1.00  
% 3.14/1.00  abstr_ref_over_cycles:                  0
% 3.14/1.00  abstr_ref_under_cycles:                 0
% 3.14/1.00  gc_basic_clause_elim:                   0
% 3.14/1.00  forced_gc_time:                         0
% 3.14/1.00  parsing_time:                           0.009
% 3.14/1.00  unif_index_cands_time:                  0.
% 3.14/1.00  unif_index_add_time:                    0.
% 3.14/1.00  orderings_time:                         0.
% 3.14/1.00  out_proof_time:                         0.012
% 3.14/1.00  total_time:                             0.271
% 3.14/1.00  num_of_symbols:                         52
% 3.14/1.00  num_of_terms:                           6980
% 3.14/1.00  
% 3.14/1.00  ------ Preprocessing
% 3.14/1.00  
% 3.14/1.00  num_of_splits:                          0
% 3.14/1.00  num_of_split_atoms:                     0
% 3.14/1.00  num_of_reused_defs:                     0
% 3.14/1.00  num_eq_ax_congr_red:                    6
% 3.14/1.00  num_of_sem_filtered_clauses:            1
% 3.14/1.00  num_of_subtypes:                        0
% 3.14/1.00  monotx_restored_types:                  0
% 3.14/1.00  sat_num_of_epr_types:                   0
% 3.14/1.00  sat_num_of_non_cyclic_types:            0
% 3.14/1.00  sat_guarded_non_collapsed_types:        0
% 3.14/1.00  num_pure_diseq_elim:                    0
% 3.14/1.00  simp_replaced_by:                       0
% 3.14/1.00  res_preprocessed:                       160
% 3.14/1.00  prep_upred:                             0
% 3.14/1.00  prep_unflattend:                        16
% 3.14/1.00  smt_new_axioms:                         0
% 3.14/1.00  pred_elim_cands:                        4
% 3.14/1.00  pred_elim:                              2
% 3.14/1.00  pred_elim_cl:                           3
% 3.14/1.00  pred_elim_cycles:                       4
% 3.14/1.00  merged_defs:                            0
% 3.14/1.00  merged_defs_ncl:                        0
% 3.14/1.00  bin_hyper_res:                          0
% 3.14/1.00  prep_cycles:                            4
% 3.14/1.00  pred_elim_time:                         0.006
% 3.14/1.00  splitting_time:                         0.
% 3.14/1.00  sem_filter_time:                        0.
% 3.14/1.00  monotx_time:                            0.001
% 3.14/1.00  subtype_inf_time:                       0.
% 3.14/1.00  
% 3.14/1.00  ------ Problem properties
% 3.14/1.00  
% 3.14/1.00  clauses:                                31
% 3.14/1.00  conjectures:                            10
% 3.14/1.00  epr:                                    6
% 3.14/1.00  horn:                                   25
% 3.14/1.00  ground:                                 13
% 3.14/1.00  unary:                                  11
% 3.14/1.00  binary:                                 3
% 3.14/1.00  lits:                                   87
% 3.14/1.00  lits_eq:                                30
% 3.14/1.00  fd_pure:                                0
% 3.14/1.00  fd_pseudo:                              0
% 3.14/1.00  fd_cond:                                6
% 3.14/1.00  fd_pseudo_cond:                         0
% 3.14/1.00  ac_symbols:                             0
% 3.14/1.00  
% 3.14/1.00  ------ Propositional Solver
% 3.14/1.00  
% 3.14/1.00  prop_solver_calls:                      30
% 3.14/1.00  prop_fast_solver_calls:                 1292
% 3.14/1.00  smt_solver_calls:                       0
% 3.14/1.00  smt_fast_solver_calls:                  0
% 3.14/1.00  prop_num_of_clauses:                    2830
% 3.14/1.00  prop_preprocess_simplified:             6890
% 3.14/1.00  prop_fo_subsumed:                       73
% 3.14/1.00  prop_solver_time:                       0.
% 3.14/1.00  smt_solver_time:                        0.
% 3.14/1.00  smt_fast_solver_time:                   0.
% 3.14/1.00  prop_fast_solver_time:                  0.
% 3.14/1.00  prop_unsat_core_time:                   0.
% 3.14/1.00  
% 3.14/1.00  ------ QBF
% 3.14/1.00  
% 3.14/1.00  qbf_q_res:                              0
% 3.14/1.00  qbf_num_tautologies:                    0
% 3.14/1.00  qbf_prep_cycles:                        0
% 3.14/1.00  
% 3.14/1.00  ------ BMC1
% 3.14/1.00  
% 3.14/1.00  bmc1_current_bound:                     -1
% 3.14/1.00  bmc1_last_solved_bound:                 -1
% 3.14/1.00  bmc1_unsat_core_size:                   -1
% 3.14/1.00  bmc1_unsat_core_parents_size:           -1
% 3.14/1.00  bmc1_merge_next_fun:                    0
% 3.14/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.14/1.00  
% 3.14/1.00  ------ Instantiation
% 3.14/1.00  
% 3.14/1.00  inst_num_of_clauses:                    822
% 3.14/1.00  inst_num_in_passive:                    361
% 3.14/1.00  inst_num_in_active:                     441
% 3.14/1.00  inst_num_in_unprocessed:                20
% 3.14/1.00  inst_num_of_loops:                      450
% 3.14/1.00  inst_num_of_learning_restarts:          0
% 3.14/1.00  inst_num_moves_active_passive:          5
% 3.14/1.00  inst_lit_activity:                      0
% 3.14/1.00  inst_lit_activity_moves:                0
% 3.14/1.00  inst_num_tautologies:                   0
% 3.14/1.00  inst_num_prop_implied:                  0
% 3.14/1.00  inst_num_existing_simplified:           0
% 3.14/1.00  inst_num_eq_res_simplified:             0
% 3.14/1.00  inst_num_child_elim:                    0
% 3.14/1.00  inst_num_of_dismatching_blockings:      53
% 3.14/1.00  inst_num_of_non_proper_insts:           606
% 3.14/1.00  inst_num_of_duplicates:                 0
% 3.14/1.00  inst_inst_num_from_inst_to_res:         0
% 3.14/1.00  inst_dismatching_checking_time:         0.
% 3.14/1.00  
% 3.14/1.00  ------ Resolution
% 3.14/1.00  
% 3.14/1.00  res_num_of_clauses:                     0
% 3.14/1.00  res_num_in_passive:                     0
% 3.14/1.00  res_num_in_active:                      0
% 3.14/1.00  res_num_of_loops:                       164
% 3.14/1.00  res_forward_subset_subsumed:            69
% 3.14/1.00  res_backward_subset_subsumed:           0
% 3.14/1.00  res_forward_subsumed:                   0
% 3.14/1.00  res_backward_subsumed:                  0
% 3.14/1.00  res_forward_subsumption_resolution:     0
% 3.14/1.00  res_backward_subsumption_resolution:    0
% 3.14/1.00  res_clause_to_clause_subsumption:       189
% 3.14/1.00  res_orphan_elimination:                 0
% 3.14/1.00  res_tautology_del:                      32
% 3.14/1.00  res_num_eq_res_simplified:              0
% 3.14/1.00  res_num_sel_changes:                    0
% 3.14/1.00  res_moves_from_active_to_pass:          0
% 3.14/1.00  
% 3.14/1.00  ------ Superposition
% 3.14/1.00  
% 3.14/1.00  sup_time_total:                         0.
% 3.14/1.00  sup_time_generating:                    0.
% 3.14/1.00  sup_time_sim_full:                      0.
% 3.14/1.00  sup_time_sim_immed:                     0.
% 3.14/1.00  
% 3.14/1.00  sup_num_of_clauses:                     131
% 3.14/1.00  sup_num_in_active:                      78
% 3.14/1.00  sup_num_in_passive:                     53
% 3.14/1.00  sup_num_of_loops:                       89
% 3.14/1.00  sup_fw_superposition:                   34
% 3.14/1.00  sup_bw_superposition:                   76
% 3.14/1.00  sup_immediate_simplified:               15
% 3.14/1.00  sup_given_eliminated:                   0
% 3.14/1.00  comparisons_done:                       0
% 3.14/1.00  comparisons_avoided:                    0
% 3.14/1.00  
% 3.14/1.00  ------ Simplifications
% 3.14/1.00  
% 3.14/1.00  
% 3.14/1.00  sim_fw_subset_subsumed:                 6
% 3.14/1.00  sim_bw_subset_subsumed:                 3
% 3.14/1.00  sim_fw_subsumed:                        0
% 3.14/1.00  sim_bw_subsumed:                        0
% 3.14/1.00  sim_fw_subsumption_res:                 0
% 3.14/1.00  sim_bw_subsumption_res:                 0
% 3.14/1.00  sim_tautology_del:                      0
% 3.14/1.00  sim_eq_tautology_del:                   4
% 3.14/1.00  sim_eq_res_simp:                        0
% 3.14/1.00  sim_fw_demodulated:                     6
% 3.14/1.00  sim_bw_demodulated:                     10
% 3.14/1.00  sim_light_normalised:                   3
% 3.14/1.00  sim_joinable_taut:                      0
% 3.14/1.00  sim_joinable_simp:                      0
% 3.14/1.00  sim_ac_normalised:                      0
% 3.14/1.00  sim_smt_subsumption:                    0
% 3.14/1.00  
%------------------------------------------------------------------------------
