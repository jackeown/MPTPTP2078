%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:38 EST 2020

% Result     : Theorem 7.67s
% Output     : CNFRefutation 7.67s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 837 expanded)
%              Number of clauses        :  110 ( 269 expanded)
%              Number of leaves         :   20 ( 202 expanded)
%              Depth                    :   22
%              Number of atoms          :  597 (5617 expanded)
%              Number of equality atoms :  274 (1897 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f41])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f42,f48,f47])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1177,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1186,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1810,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1186])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1179,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1809,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1186])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1195,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2795,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1809,c_1195])).

cnf(c_3048,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1810,c_2795])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1178,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1189,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3524,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1189])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_45,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3767,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3524,c_45,c_1809])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1190,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3770,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3767,c_1190])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2589,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2590,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2589])).

cnf(c_4151,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3770,c_42,c_45,c_1809,c_2590])).

cnf(c_4158,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3048,c_4151])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7618,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7619,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7618])).

cnf(c_15796,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4158,c_42,c_45,c_1809,c_7619])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1184,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2708,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1184])).

cnf(c_5384,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_2708])).

cnf(c_5689,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5384,c_42])).

cnf(c_5690,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5689])).

cnf(c_5697,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_5690])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1181,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4369,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1181])).

cnf(c_4429,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4369,c_42])).

cnf(c_4430,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4429])).

cnf(c_4437,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_4430])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_4510,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4437,c_39])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_4512,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4510,c_32])).

cnf(c_5701,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5697,c_4510,c_4512])).

cnf(c_5710,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5701,c_39])).

cnf(c_1191,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2918,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1195])).

cnf(c_8059,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_2918])).

cnf(c_8594,plain,
    ( v1_relat_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8059,c_45,c_1809])).

cnf(c_8595,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8594])).

cnf(c_8601,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_1809,c_8595])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1187,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3276,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_1187])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1185,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2037,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1179,c_1185])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_481,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_484,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_482,c_33,c_30])).

cnf(c_2039,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2037,c_484])).

cnf(c_3278,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3276,c_2039])).

cnf(c_3870,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3278,c_45,c_1809])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1194,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5714,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5710,c_1194])).

cnf(c_5961,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5714,c_1809,c_1810])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_387,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_391,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_387,c_16])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_391])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_392])).

cnf(c_1901,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1175])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1197,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2206,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1901,c_1197])).

cnf(c_5966,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_5961,c_2206])).

cnf(c_8608,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8601,c_3870,c_5966])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8609,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8608,c_7])).

cnf(c_15800,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15796,c_5710,c_8609])).

cnf(c_2035,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1177,c_1184])).

cnf(c_708,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1237,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_1798,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1237])).

cnf(c_1264,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1314,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(X0))
    | sK1 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1264])).

cnf(c_1668,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | sK1 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_1669,plain,
    ( sK1 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1668])).

cnf(c_1411,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | r1_tarski(k2_relat_1(X0),sK1) ),
    inference(instantiation,[status(thm)],[c_392])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_1562,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15800,c_2035,c_1798,c_1669,c_1562,c_29,c_41])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:04:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.26/1.43  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.26/1.43  
% 7.26/1.43  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.26/1.43  
% 7.26/1.43  ------  iProver source info
% 7.26/1.43  
% 7.26/1.43  git: date: 2020-06-30 10:37:57 +0100
% 7.26/1.43  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.26/1.43  git: non_committed_changes: false
% 7.26/1.43  git: last_make_outside_of_git: false
% 7.26/1.43  
% 7.26/1.43  ------ 
% 7.26/1.43  
% 7.26/1.43  ------ Input Options
% 7.26/1.43  
% 7.26/1.43  --out_options                           all
% 7.26/1.43  --tptp_safe_out                         true
% 7.26/1.43  --problem_path                          ""
% 7.26/1.43  --include_path                          ""
% 7.26/1.43  --clausifier                            res/vclausify_rel
% 7.26/1.43  --clausifier_options                    ""
% 7.26/1.43  --stdin                                 false
% 7.26/1.43  --stats_out                             all
% 7.26/1.43  
% 7.26/1.43  ------ General Options
% 7.26/1.43  
% 7.26/1.43  --fof                                   false
% 7.26/1.43  --time_out_real                         305.
% 7.26/1.43  --time_out_virtual                      -1.
% 7.26/1.43  --symbol_type_check                     false
% 7.26/1.43  --clausify_out                          false
% 7.26/1.43  --sig_cnt_out                           false
% 7.26/1.43  --trig_cnt_out                          false
% 7.26/1.43  --trig_cnt_out_tolerance                1.
% 7.26/1.43  --trig_cnt_out_sk_spl                   false
% 7.26/1.43  --abstr_cl_out                          false
% 7.26/1.43  
% 7.26/1.43  ------ Global Options
% 7.26/1.43  
% 7.26/1.43  --schedule                              default
% 7.26/1.43  --add_important_lit                     false
% 7.26/1.43  --prop_solver_per_cl                    1000
% 7.26/1.43  --min_unsat_core                        false
% 7.26/1.43  --soft_assumptions                      false
% 7.26/1.43  --soft_lemma_size                       3
% 7.26/1.43  --prop_impl_unit_size                   0
% 7.26/1.43  --prop_impl_unit                        []
% 7.26/1.43  --share_sel_clauses                     true
% 7.26/1.43  --reset_solvers                         false
% 7.26/1.43  --bc_imp_inh                            [conj_cone]
% 7.26/1.43  --conj_cone_tolerance                   3.
% 7.26/1.43  --extra_neg_conj                        none
% 7.26/1.43  --large_theory_mode                     true
% 7.26/1.43  --prolific_symb_bound                   200
% 7.26/1.43  --lt_threshold                          2000
% 7.26/1.43  --clause_weak_htbl                      true
% 7.26/1.43  --gc_record_bc_elim                     false
% 7.26/1.43  
% 7.26/1.43  ------ Preprocessing Options
% 7.26/1.43  
% 7.26/1.43  --preprocessing_flag                    true
% 7.26/1.43  --time_out_prep_mult                    0.1
% 7.26/1.43  --splitting_mode                        input
% 7.26/1.43  --splitting_grd                         true
% 7.26/1.43  --splitting_cvd                         false
% 7.26/1.43  --splitting_cvd_svl                     false
% 7.26/1.43  --splitting_nvd                         32
% 7.26/1.43  --sub_typing                            true
% 7.26/1.43  --prep_gs_sim                           true
% 7.26/1.43  --prep_unflatten                        true
% 7.26/1.43  --prep_res_sim                          true
% 7.26/1.43  --prep_upred                            true
% 7.26/1.43  --prep_sem_filter                       exhaustive
% 7.26/1.43  --prep_sem_filter_out                   false
% 7.26/1.43  --pred_elim                             true
% 7.26/1.43  --res_sim_input                         true
% 7.26/1.43  --eq_ax_congr_red                       true
% 7.26/1.43  --pure_diseq_elim                       true
% 7.26/1.43  --brand_transform                       false
% 7.26/1.43  --non_eq_to_eq                          false
% 7.26/1.43  --prep_def_merge                        true
% 7.26/1.43  --prep_def_merge_prop_impl              false
% 7.26/1.43  --prep_def_merge_mbd                    true
% 7.26/1.43  --prep_def_merge_tr_red                 false
% 7.26/1.43  --prep_def_merge_tr_cl                  false
% 7.26/1.43  --smt_preprocessing                     true
% 7.26/1.43  --smt_ac_axioms                         fast
% 7.26/1.43  --preprocessed_out                      false
% 7.26/1.43  --preprocessed_stats                    false
% 7.26/1.43  
% 7.26/1.43  ------ Abstraction refinement Options
% 7.26/1.43  
% 7.26/1.43  --abstr_ref                             []
% 7.26/1.43  --abstr_ref_prep                        false
% 7.26/1.43  --abstr_ref_until_sat                   false
% 7.26/1.43  --abstr_ref_sig_restrict                funpre
% 7.26/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.26/1.43  --abstr_ref_under                       []
% 7.26/1.43  
% 7.26/1.43  ------ SAT Options
% 7.26/1.43  
% 7.26/1.43  --sat_mode                              false
% 7.26/1.43  --sat_fm_restart_options                ""
% 7.26/1.43  --sat_gr_def                            false
% 7.26/1.43  --sat_epr_types                         true
% 7.26/1.43  --sat_non_cyclic_types                  false
% 7.26/1.43  --sat_finite_models                     false
% 7.26/1.43  --sat_fm_lemmas                         false
% 7.26/1.43  --sat_fm_prep                           false
% 7.26/1.43  --sat_fm_uc_incr                        true
% 7.26/1.43  --sat_out_model                         small
% 7.26/1.43  --sat_out_clauses                       false
% 7.26/1.43  
% 7.26/1.43  ------ QBF Options
% 7.26/1.43  
% 7.26/1.43  --qbf_mode                              false
% 7.26/1.43  --qbf_elim_univ                         false
% 7.26/1.43  --qbf_dom_inst                          none
% 7.26/1.43  --qbf_dom_pre_inst                      false
% 7.26/1.43  --qbf_sk_in                             false
% 7.26/1.43  --qbf_pred_elim                         true
% 7.26/1.43  --qbf_split                             512
% 7.26/1.43  
% 7.26/1.43  ------ BMC1 Options
% 7.26/1.43  
% 7.26/1.43  --bmc1_incremental                      false
% 7.26/1.43  --bmc1_axioms                           reachable_all
% 7.26/1.43  --bmc1_min_bound                        0
% 7.26/1.43  --bmc1_max_bound                        -1
% 7.26/1.43  --bmc1_max_bound_default                -1
% 7.26/1.43  --bmc1_symbol_reachability              true
% 7.26/1.43  --bmc1_property_lemmas                  false
% 7.26/1.43  --bmc1_k_induction                      false
% 7.26/1.43  --bmc1_non_equiv_states                 false
% 7.26/1.43  --bmc1_deadlock                         false
% 7.26/1.43  --bmc1_ucm                              false
% 7.26/1.43  --bmc1_add_unsat_core                   none
% 7.26/1.43  --bmc1_unsat_core_children              false
% 7.26/1.43  --bmc1_unsat_core_extrapolate_axioms    false
% 7.26/1.43  --bmc1_out_stat                         full
% 7.26/1.43  --bmc1_ground_init                      false
% 7.26/1.43  --bmc1_pre_inst_next_state              false
% 7.26/1.43  --bmc1_pre_inst_state                   false
% 7.26/1.43  --bmc1_pre_inst_reach_state             false
% 7.26/1.43  --bmc1_out_unsat_core                   false
% 7.26/1.43  --bmc1_aig_witness_out                  false
% 7.26/1.43  --bmc1_verbose                          false
% 7.26/1.43  --bmc1_dump_clauses_tptp                false
% 7.26/1.43  --bmc1_dump_unsat_core_tptp             false
% 7.26/1.43  --bmc1_dump_file                        -
% 7.26/1.43  --bmc1_ucm_expand_uc_limit              128
% 7.26/1.43  --bmc1_ucm_n_expand_iterations          6
% 7.26/1.43  --bmc1_ucm_extend_mode                  1
% 7.26/1.43  --bmc1_ucm_init_mode                    2
% 7.26/1.43  --bmc1_ucm_cone_mode                    none
% 7.26/1.43  --bmc1_ucm_reduced_relation_type        0
% 7.26/1.43  --bmc1_ucm_relax_model                  4
% 7.26/1.43  --bmc1_ucm_full_tr_after_sat            true
% 7.26/1.43  --bmc1_ucm_expand_neg_assumptions       false
% 7.26/1.43  --bmc1_ucm_layered_model                none
% 7.26/1.43  --bmc1_ucm_max_lemma_size               10
% 7.26/1.43  
% 7.26/1.43  ------ AIG Options
% 7.26/1.43  
% 7.26/1.43  --aig_mode                              false
% 7.26/1.43  
% 7.26/1.43  ------ Instantiation Options
% 7.26/1.43  
% 7.26/1.43  --instantiation_flag                    true
% 7.26/1.43  --inst_sos_flag                         true
% 7.26/1.43  --inst_sos_phase                        true
% 7.26/1.43  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.26/1.43  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.26/1.43  --inst_lit_sel_side                     num_symb
% 7.26/1.43  --inst_solver_per_active                1400
% 7.26/1.43  --inst_solver_calls_frac                1.
% 7.26/1.43  --inst_passive_queue_type               priority_queues
% 7.26/1.43  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.26/1.43  --inst_passive_queues_freq              [25;2]
% 7.26/1.43  --inst_dismatching                      true
% 7.26/1.43  --inst_eager_unprocessed_to_passive     true
% 7.26/1.43  --inst_prop_sim_given                   true
% 7.26/1.43  --inst_prop_sim_new                     false
% 7.26/1.43  --inst_subs_new                         false
% 7.26/1.43  --inst_eq_res_simp                      false
% 7.26/1.43  --inst_subs_given                       false
% 7.26/1.43  --inst_orphan_elimination               true
% 7.26/1.43  --inst_learning_loop_flag               true
% 7.26/1.43  --inst_learning_start                   3000
% 7.26/1.43  --inst_learning_factor                  2
% 7.26/1.43  --inst_start_prop_sim_after_learn       3
% 7.26/1.43  --inst_sel_renew                        solver
% 7.26/1.43  --inst_lit_activity_flag                true
% 7.26/1.43  --inst_restr_to_given                   false
% 7.26/1.43  --inst_activity_threshold               500
% 7.26/1.43  --inst_out_proof                        true
% 7.26/1.43  
% 7.26/1.43  ------ Resolution Options
% 7.26/1.43  
% 7.26/1.43  --resolution_flag                       true
% 7.26/1.43  --res_lit_sel                           adaptive
% 7.26/1.43  --res_lit_sel_side                      none
% 7.26/1.43  --res_ordering                          kbo
% 7.26/1.43  --res_to_prop_solver                    active
% 7.26/1.43  --res_prop_simpl_new                    false
% 7.26/1.43  --res_prop_simpl_given                  true
% 7.26/1.43  --res_passive_queue_type                priority_queues
% 7.26/1.43  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.26/1.43  --res_passive_queues_freq               [15;5]
% 7.26/1.43  --res_forward_subs                      full
% 7.26/1.43  --res_backward_subs                     full
% 7.26/1.43  --res_forward_subs_resolution           true
% 7.26/1.43  --res_backward_subs_resolution          true
% 7.26/1.43  --res_orphan_elimination                true
% 7.26/1.43  --res_time_limit                        2.
% 7.26/1.43  --res_out_proof                         true
% 7.26/1.43  
% 7.26/1.43  ------ Superposition Options
% 7.26/1.43  
% 7.26/1.43  --superposition_flag                    true
% 7.26/1.43  --sup_passive_queue_type                priority_queues
% 7.26/1.43  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.26/1.43  --sup_passive_queues_freq               [8;1;4]
% 7.26/1.43  --demod_completeness_check              fast
% 7.26/1.43  --demod_use_ground                      true
% 7.26/1.43  --sup_to_prop_solver                    passive
% 7.26/1.43  --sup_prop_simpl_new                    true
% 7.26/1.43  --sup_prop_simpl_given                  true
% 7.26/1.43  --sup_fun_splitting                     true
% 7.26/1.43  --sup_smt_interval                      50000
% 7.26/1.43  
% 7.26/1.43  ------ Superposition Simplification Setup
% 7.26/1.43  
% 7.26/1.43  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.26/1.43  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.26/1.43  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.26/1.43  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.26/1.43  --sup_full_triv                         [TrivRules;PropSubs]
% 7.26/1.43  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.26/1.43  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.26/1.43  --sup_immed_triv                        [TrivRules]
% 7.26/1.43  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.43  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.43  --sup_immed_bw_main                     []
% 7.26/1.43  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.26/1.43  --sup_input_triv                        [Unflattening;TrivRules]
% 7.26/1.43  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.26/1.43  --sup_input_bw                          []
% 7.26/1.43  
% 7.26/1.43  ------ Combination Options
% 7.26/1.43  
% 7.26/1.43  --comb_res_mult                         3
% 7.26/1.43  --comb_sup_mult                         2
% 7.26/1.43  --comb_inst_mult                        10
% 7.26/1.43  
% 7.26/1.43  ------ Debug Options
% 7.26/1.43  
% 7.26/1.43  --dbg_backtrace                         false
% 7.26/1.43  --dbg_dump_prop_clauses                 false
% 7.26/1.43  --dbg_dump_prop_clauses_file            -
% 7.26/1.43  --dbg_out_stat                          false
% 7.26/1.43  ------ Parsing...
% 7.26/1.43  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.26/1.43  
% 7.26/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.26/1.43  
% 7.26/1.43  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.26/1.43  
% 7.26/1.43  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.26/1.43  ------ Proving...
% 7.26/1.43  ------ Problem Properties 
% 7.26/1.43  
% 7.26/1.43  
% 7.26/1.43  clauses                                 34
% 7.26/1.43  conjectures                             8
% 7.26/1.43  EPR                                     6
% 7.26/1.43  Horn                                    31
% 7.26/1.43  unary                                   12
% 7.67/1.43  binary                                  5
% 7.67/1.43  lits                                    87
% 7.67/1.43  lits eq                                 26
% 7.67/1.43  fd_pure                                 0
% 7.67/1.43  fd_pseudo                               0
% 7.67/1.43  fd_cond                                 0
% 7.67/1.43  fd_pseudo_cond                          1
% 7.67/1.43  AC symbols                              0
% 7.67/1.43  
% 7.67/1.43  ------ Schedule dynamic 5 is on 
% 7.67/1.43  
% 7.67/1.43  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.67/1.43  
% 7.67/1.43  
% 7.67/1.43  ------ 
% 7.67/1.43  Current options:
% 7.67/1.43  ------ 
% 7.67/1.43  
% 7.67/1.43  ------ Input Options
% 7.67/1.43  
% 7.67/1.43  --out_options                           all
% 7.67/1.43  --tptp_safe_out                         true
% 7.67/1.43  --problem_path                          ""
% 7.67/1.43  --include_path                          ""
% 7.67/1.43  --clausifier                            res/vclausify_rel
% 7.67/1.43  --clausifier_options                    ""
% 7.67/1.43  --stdin                                 false
% 7.67/1.43  --stats_out                             all
% 7.67/1.43  
% 7.67/1.43  ------ General Options
% 7.67/1.43  
% 7.67/1.43  --fof                                   false
% 7.67/1.43  --time_out_real                         305.
% 7.67/1.43  --time_out_virtual                      -1.
% 7.67/1.43  --symbol_type_check                     false
% 7.67/1.43  --clausify_out                          false
% 7.67/1.43  --sig_cnt_out                           false
% 7.67/1.43  --trig_cnt_out                          false
% 7.67/1.43  --trig_cnt_out_tolerance                1.
% 7.67/1.43  --trig_cnt_out_sk_spl                   false
% 7.67/1.43  --abstr_cl_out                          false
% 7.67/1.43  
% 7.67/1.43  ------ Global Options
% 7.67/1.43  
% 7.67/1.43  --schedule                              default
% 7.67/1.43  --add_important_lit                     false
% 7.67/1.43  --prop_solver_per_cl                    1000
% 7.67/1.43  --min_unsat_core                        false
% 7.67/1.43  --soft_assumptions                      false
% 7.67/1.43  --soft_lemma_size                       3
% 7.67/1.43  --prop_impl_unit_size                   0
% 7.67/1.43  --prop_impl_unit                        []
% 7.67/1.43  --share_sel_clauses                     true
% 7.67/1.43  --reset_solvers                         false
% 7.67/1.43  --bc_imp_inh                            [conj_cone]
% 7.67/1.43  --conj_cone_tolerance                   3.
% 7.67/1.43  --extra_neg_conj                        none
% 7.67/1.43  --large_theory_mode                     true
% 7.67/1.43  --prolific_symb_bound                   200
% 7.67/1.43  --lt_threshold                          2000
% 7.67/1.43  --clause_weak_htbl                      true
% 7.67/1.43  --gc_record_bc_elim                     false
% 7.67/1.43  
% 7.67/1.43  ------ Preprocessing Options
% 7.67/1.43  
% 7.67/1.43  --preprocessing_flag                    true
% 7.67/1.43  --time_out_prep_mult                    0.1
% 7.67/1.43  --splitting_mode                        input
% 7.67/1.43  --splitting_grd                         true
% 7.67/1.43  --splitting_cvd                         false
% 7.67/1.43  --splitting_cvd_svl                     false
% 7.67/1.43  --splitting_nvd                         32
% 7.67/1.43  --sub_typing                            true
% 7.67/1.43  --prep_gs_sim                           true
% 7.67/1.43  --prep_unflatten                        true
% 7.67/1.43  --prep_res_sim                          true
% 7.67/1.43  --prep_upred                            true
% 7.67/1.43  --prep_sem_filter                       exhaustive
% 7.67/1.43  --prep_sem_filter_out                   false
% 7.67/1.43  --pred_elim                             true
% 7.67/1.43  --res_sim_input                         true
% 7.67/1.43  --eq_ax_congr_red                       true
% 7.67/1.43  --pure_diseq_elim                       true
% 7.67/1.43  --brand_transform                       false
% 7.67/1.43  --non_eq_to_eq                          false
% 7.67/1.43  --prep_def_merge                        true
% 7.67/1.43  --prep_def_merge_prop_impl              false
% 7.67/1.43  --prep_def_merge_mbd                    true
% 7.67/1.43  --prep_def_merge_tr_red                 false
% 7.67/1.43  --prep_def_merge_tr_cl                  false
% 7.67/1.43  --smt_preprocessing                     true
% 7.67/1.43  --smt_ac_axioms                         fast
% 7.67/1.43  --preprocessed_out                      false
% 7.67/1.43  --preprocessed_stats                    false
% 7.67/1.43  
% 7.67/1.43  ------ Abstraction refinement Options
% 7.67/1.43  
% 7.67/1.43  --abstr_ref                             []
% 7.67/1.43  --abstr_ref_prep                        false
% 7.67/1.43  --abstr_ref_until_sat                   false
% 7.67/1.43  --abstr_ref_sig_restrict                funpre
% 7.67/1.43  --abstr_ref_af_restrict_to_split_sk     false
% 7.67/1.43  --abstr_ref_under                       []
% 7.67/1.43  
% 7.67/1.43  ------ SAT Options
% 7.67/1.43  
% 7.67/1.43  --sat_mode                              false
% 7.67/1.43  --sat_fm_restart_options                ""
% 7.67/1.43  --sat_gr_def                            false
% 7.67/1.43  --sat_epr_types                         true
% 7.67/1.43  --sat_non_cyclic_types                  false
% 7.67/1.44  --sat_finite_models                     false
% 7.67/1.44  --sat_fm_lemmas                         false
% 7.67/1.44  --sat_fm_prep                           false
% 7.67/1.44  --sat_fm_uc_incr                        true
% 7.67/1.44  --sat_out_model                         small
% 7.67/1.44  --sat_out_clauses                       false
% 7.67/1.44  
% 7.67/1.44  ------ QBF Options
% 7.67/1.44  
% 7.67/1.44  --qbf_mode                              false
% 7.67/1.44  --qbf_elim_univ                         false
% 7.67/1.44  --qbf_dom_inst                          none
% 7.67/1.44  --qbf_dom_pre_inst                      false
% 7.67/1.44  --qbf_sk_in                             false
% 7.67/1.44  --qbf_pred_elim                         true
% 7.67/1.44  --qbf_split                             512
% 7.67/1.44  
% 7.67/1.44  ------ BMC1 Options
% 7.67/1.44  
% 7.67/1.44  --bmc1_incremental                      false
% 7.67/1.44  --bmc1_axioms                           reachable_all
% 7.67/1.44  --bmc1_min_bound                        0
% 7.67/1.44  --bmc1_max_bound                        -1
% 7.67/1.44  --bmc1_max_bound_default                -1
% 7.67/1.44  --bmc1_symbol_reachability              true
% 7.67/1.44  --bmc1_property_lemmas                  false
% 7.67/1.44  --bmc1_k_induction                      false
% 7.67/1.44  --bmc1_non_equiv_states                 false
% 7.67/1.44  --bmc1_deadlock                         false
% 7.67/1.44  --bmc1_ucm                              false
% 7.67/1.44  --bmc1_add_unsat_core                   none
% 7.67/1.44  --bmc1_unsat_core_children              false
% 7.67/1.44  --bmc1_unsat_core_extrapolate_axioms    false
% 7.67/1.44  --bmc1_out_stat                         full
% 7.67/1.44  --bmc1_ground_init                      false
% 7.67/1.44  --bmc1_pre_inst_next_state              false
% 7.67/1.44  --bmc1_pre_inst_state                   false
% 7.67/1.44  --bmc1_pre_inst_reach_state             false
% 7.67/1.44  --bmc1_out_unsat_core                   false
% 7.67/1.44  --bmc1_aig_witness_out                  false
% 7.67/1.44  --bmc1_verbose                          false
% 7.67/1.44  --bmc1_dump_clauses_tptp                false
% 7.67/1.44  --bmc1_dump_unsat_core_tptp             false
% 7.67/1.44  --bmc1_dump_file                        -
% 7.67/1.44  --bmc1_ucm_expand_uc_limit              128
% 7.67/1.44  --bmc1_ucm_n_expand_iterations          6
% 7.67/1.44  --bmc1_ucm_extend_mode                  1
% 7.67/1.44  --bmc1_ucm_init_mode                    2
% 7.67/1.44  --bmc1_ucm_cone_mode                    none
% 7.67/1.44  --bmc1_ucm_reduced_relation_type        0
% 7.67/1.44  --bmc1_ucm_relax_model                  4
% 7.67/1.44  --bmc1_ucm_full_tr_after_sat            true
% 7.67/1.44  --bmc1_ucm_expand_neg_assumptions       false
% 7.67/1.44  --bmc1_ucm_layered_model                none
% 7.67/1.44  --bmc1_ucm_max_lemma_size               10
% 7.67/1.44  
% 7.67/1.44  ------ AIG Options
% 7.67/1.44  
% 7.67/1.44  --aig_mode                              false
% 7.67/1.44  
% 7.67/1.44  ------ Instantiation Options
% 7.67/1.44  
% 7.67/1.44  --instantiation_flag                    true
% 7.67/1.44  --inst_sos_flag                         true
% 7.67/1.44  --inst_sos_phase                        true
% 7.67/1.44  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.67/1.44  --inst_lit_sel_side                     none
% 7.67/1.44  --inst_solver_per_active                1400
% 7.67/1.44  --inst_solver_calls_frac                1.
% 7.67/1.44  --inst_passive_queue_type               priority_queues
% 7.67/1.44  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.67/1.44  --inst_passive_queues_freq              [25;2]
% 7.67/1.44  --inst_dismatching                      true
% 7.67/1.44  --inst_eager_unprocessed_to_passive     true
% 7.67/1.44  --inst_prop_sim_given                   true
% 7.67/1.44  --inst_prop_sim_new                     false
% 7.67/1.44  --inst_subs_new                         false
% 7.67/1.44  --inst_eq_res_simp                      false
% 7.67/1.44  --inst_subs_given                       false
% 7.67/1.44  --inst_orphan_elimination               true
% 7.67/1.44  --inst_learning_loop_flag               true
% 7.67/1.44  --inst_learning_start                   3000
% 7.67/1.44  --inst_learning_factor                  2
% 7.67/1.44  --inst_start_prop_sim_after_learn       3
% 7.67/1.44  --inst_sel_renew                        solver
% 7.67/1.44  --inst_lit_activity_flag                true
% 7.67/1.44  --inst_restr_to_given                   false
% 7.67/1.44  --inst_activity_threshold               500
% 7.67/1.44  --inst_out_proof                        true
% 7.67/1.44  
% 7.67/1.44  ------ Resolution Options
% 7.67/1.44  
% 7.67/1.44  --resolution_flag                       false
% 7.67/1.44  --res_lit_sel                           adaptive
% 7.67/1.44  --res_lit_sel_side                      none
% 7.67/1.44  --res_ordering                          kbo
% 7.67/1.44  --res_to_prop_solver                    active
% 7.67/1.44  --res_prop_simpl_new                    false
% 7.67/1.44  --res_prop_simpl_given                  true
% 7.67/1.44  --res_passive_queue_type                priority_queues
% 7.67/1.44  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.67/1.44  --res_passive_queues_freq               [15;5]
% 7.67/1.44  --res_forward_subs                      full
% 7.67/1.44  --res_backward_subs                     full
% 7.67/1.44  --res_forward_subs_resolution           true
% 7.67/1.44  --res_backward_subs_resolution          true
% 7.67/1.44  --res_orphan_elimination                true
% 7.67/1.44  --res_time_limit                        2.
% 7.67/1.44  --res_out_proof                         true
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Options
% 7.67/1.44  
% 7.67/1.44  --superposition_flag                    true
% 7.67/1.44  --sup_passive_queue_type                priority_queues
% 7.67/1.44  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.67/1.44  --sup_passive_queues_freq               [8;1;4]
% 7.67/1.44  --demod_completeness_check              fast
% 7.67/1.44  --demod_use_ground                      true
% 7.67/1.44  --sup_to_prop_solver                    passive
% 7.67/1.44  --sup_prop_simpl_new                    true
% 7.67/1.44  --sup_prop_simpl_given                  true
% 7.67/1.44  --sup_fun_splitting                     true
% 7.67/1.44  --sup_smt_interval                      50000
% 7.67/1.44  
% 7.67/1.44  ------ Superposition Simplification Setup
% 7.67/1.44  
% 7.67/1.44  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.67/1.44  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.67/1.44  --sup_full_triv                         [TrivRules;PropSubs]
% 7.67/1.44  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.67/1.44  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_immed_triv                        [TrivRules]
% 7.67/1.44  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_immed_bw_main                     []
% 7.67/1.44  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.67/1.44  --sup_input_triv                        [Unflattening;TrivRules]
% 7.67/1.44  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.67/1.44  --sup_input_bw                          []
% 7.67/1.44  
% 7.67/1.44  ------ Combination Options
% 7.67/1.44  
% 7.67/1.44  --comb_res_mult                         3
% 7.67/1.44  --comb_sup_mult                         2
% 7.67/1.44  --comb_inst_mult                        10
% 7.67/1.44  
% 7.67/1.44  ------ Debug Options
% 7.67/1.44  
% 7.67/1.44  --dbg_backtrace                         false
% 7.67/1.44  --dbg_dump_prop_clauses                 false
% 7.67/1.44  --dbg_dump_prop_clauses_file            -
% 7.67/1.44  --dbg_out_stat                          false
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  ------ Proving...
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  % SZS status Theorem for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  % SZS output start CNFRefutation for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  fof(f17,conjecture,(
% 7.67/1.44    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f18,negated_conjecture,(
% 7.67/1.44    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.67/1.44    inference(negated_conjecture,[],[f17])).
% 7.67/1.44  
% 7.67/1.44  fof(f41,plain,(
% 7.67/1.44    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.67/1.44    inference(ennf_transformation,[],[f18])).
% 7.67/1.44  
% 7.67/1.44  fof(f42,plain,(
% 7.67/1.44    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.67/1.44    inference(flattening,[],[f41])).
% 7.67/1.44  
% 7.67/1.44  fof(f48,plain,(
% 7.67/1.44    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.67/1.44    introduced(choice_axiom,[])).
% 7.67/1.44  
% 7.67/1.44  fof(f47,plain,(
% 7.67/1.44    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.67/1.44    introduced(choice_axiom,[])).
% 7.67/1.44  
% 7.67/1.44  fof(f49,plain,(
% 7.67/1.44    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.67/1.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f42,f48,f47])).
% 7.67/1.44  
% 7.67/1.44  fof(f81,plain,(
% 7.67/1.44    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f10,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f31,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(ennf_transformation,[],[f10])).
% 7.67/1.44  
% 7.67/1.44  fof(f66,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f31])).
% 7.67/1.44  
% 7.67/1.44  fof(f84,plain,(
% 7.67/1.44    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f3,axiom,(
% 7.67/1.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f21,plain,(
% 7.67/1.44    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(ennf_transformation,[],[f3])).
% 7.67/1.44  
% 7.67/1.44  fof(f55,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f21])).
% 7.67/1.44  
% 7.67/1.44  fof(f82,plain,(
% 7.67/1.44    v1_funct_1(sK4)),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f8,axiom,(
% 7.67/1.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f27,plain,(
% 7.67/1.44    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.67/1.44    inference(ennf_transformation,[],[f8])).
% 7.67/1.44  
% 7.67/1.44  fof(f28,plain,(
% 7.67/1.44    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(flattening,[],[f27])).
% 7.67/1.44  
% 7.67/1.44  fof(f63,plain,(
% 7.67/1.44    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f28])).
% 7.67/1.44  
% 7.67/1.44  fof(f86,plain,(
% 7.67/1.44    v2_funct_1(sK4)),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f7,axiom,(
% 7.67/1.44    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f25,plain,(
% 7.67/1.44    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.67/1.44    inference(ennf_transformation,[],[f7])).
% 7.67/1.44  
% 7.67/1.44  fof(f26,plain,(
% 7.67/1.44    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(flattening,[],[f25])).
% 7.67/1.44  
% 7.67/1.44  fof(f62,plain,(
% 7.67/1.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f26])).
% 7.67/1.44  
% 7.67/1.44  fof(f6,axiom,(
% 7.67/1.44    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f23,plain,(
% 7.67/1.44    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.44    inference(ennf_transformation,[],[f6])).
% 7.67/1.44  
% 7.67/1.44  fof(f24,plain,(
% 7.67/1.44    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(flattening,[],[f23])).
% 7.67/1.44  
% 7.67/1.44  fof(f60,plain,(
% 7.67/1.44    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f24])).
% 7.67/1.44  
% 7.67/1.44  fof(f59,plain,(
% 7.67/1.44    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f24])).
% 7.67/1.44  
% 7.67/1.44  fof(f15,axiom,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f37,plain,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.67/1.44    inference(ennf_transformation,[],[f15])).
% 7.67/1.44  
% 7.67/1.44  fof(f38,plain,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.67/1.44    inference(flattening,[],[f37])).
% 7.67/1.44  
% 7.67/1.44  fof(f77,plain,(
% 7.67/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f38])).
% 7.67/1.44  
% 7.67/1.44  fof(f13,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f34,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(ennf_transformation,[],[f13])).
% 7.67/1.44  
% 7.67/1.44  fof(f69,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f34])).
% 7.67/1.44  
% 7.67/1.44  fof(f16,axiom,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f39,plain,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.67/1.44    inference(ennf_transformation,[],[f16])).
% 7.67/1.44  
% 7.67/1.44  fof(f40,plain,(
% 7.67/1.44    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.67/1.44    inference(flattening,[],[f39])).
% 7.67/1.44  
% 7.67/1.44  fof(f78,plain,(
% 7.67/1.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f40])).
% 7.67/1.44  
% 7.67/1.44  fof(f79,plain,(
% 7.67/1.44    v1_funct_1(sK3)),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f85,plain,(
% 7.67/1.44    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f9,axiom,(
% 7.67/1.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f29,plain,(
% 7.67/1.44    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.67/1.44    inference(ennf_transformation,[],[f9])).
% 7.67/1.44  
% 7.67/1.44  fof(f30,plain,(
% 7.67/1.44    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(flattening,[],[f29])).
% 7.67/1.44  
% 7.67/1.44  fof(f64,plain,(
% 7.67/1.44    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f30])).
% 7.67/1.44  
% 7.67/1.44  fof(f12,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f33,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(ennf_transformation,[],[f12])).
% 7.67/1.44  
% 7.67/1.44  fof(f68,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f33])).
% 7.67/1.44  
% 7.67/1.44  fof(f14,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f35,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(ennf_transformation,[],[f14])).
% 7.67/1.44  
% 7.67/1.44  fof(f36,plain,(
% 7.67/1.44    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(flattening,[],[f35])).
% 7.67/1.44  
% 7.67/1.44  fof(f46,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(nnf_transformation,[],[f36])).
% 7.67/1.44  
% 7.67/1.44  fof(f70,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f46])).
% 7.67/1.44  
% 7.67/1.44  fof(f83,plain,(
% 7.67/1.44    v1_funct_2(sK4,sK1,sK2)),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f87,plain,(
% 7.67/1.44    k1_xboole_0 != sK2),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  fof(f4,axiom,(
% 7.67/1.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f22,plain,(
% 7.67/1.44    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.67/1.44    inference(ennf_transformation,[],[f4])).
% 7.67/1.44  
% 7.67/1.44  fof(f56,plain,(
% 7.67/1.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f22])).
% 7.67/1.44  
% 7.67/1.44  fof(f2,axiom,(
% 7.67/1.44    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f20,plain,(
% 7.67/1.44    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(ennf_transformation,[],[f2])).
% 7.67/1.44  
% 7.67/1.44  fof(f45,plain,(
% 7.67/1.44    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.67/1.44    inference(nnf_transformation,[],[f20])).
% 7.67/1.44  
% 7.67/1.44  fof(f53,plain,(
% 7.67/1.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f45])).
% 7.67/1.44  
% 7.67/1.44  fof(f11,axiom,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f19,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.67/1.44    inference(pure_predicate_removal,[],[f11])).
% 7.67/1.44  
% 7.67/1.44  fof(f32,plain,(
% 7.67/1.44    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.67/1.44    inference(ennf_transformation,[],[f19])).
% 7.67/1.44  
% 7.67/1.44  fof(f67,plain,(
% 7.67/1.44    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.67/1.44    inference(cnf_transformation,[],[f32])).
% 7.67/1.44  
% 7.67/1.44  fof(f1,axiom,(
% 7.67/1.44    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f43,plain,(
% 7.67/1.44    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.44    inference(nnf_transformation,[],[f1])).
% 7.67/1.44  
% 7.67/1.44  fof(f44,plain,(
% 7.67/1.44    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.67/1.44    inference(flattening,[],[f43])).
% 7.67/1.44  
% 7.67/1.44  fof(f52,plain,(
% 7.67/1.44    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.67/1.44    inference(cnf_transformation,[],[f44])).
% 7.67/1.44  
% 7.67/1.44  fof(f5,axiom,(
% 7.67/1.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.67/1.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.67/1.44  
% 7.67/1.44  fof(f58,plain,(
% 7.67/1.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.67/1.44    inference(cnf_transformation,[],[f5])).
% 7.67/1.44  
% 7.67/1.44  fof(f88,plain,(
% 7.67/1.44    k2_relset_1(sK0,sK1,sK3) != sK1),
% 7.67/1.44    inference(cnf_transformation,[],[f49])).
% 7.67/1.44  
% 7.67/1.44  cnf(c_36,negated_conjecture,
% 7.67/1.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.67/1.44      inference(cnf_transformation,[],[f81]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1177,plain,
% 7.67/1.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_16,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f66]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1186,plain,
% 7.67/1.44      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1810,plain,
% 7.67/1.44      ( v1_relat_1(sK3) = iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1177,c_1186]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_33,negated_conjecture,
% 7.67/1.44      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.67/1.44      inference(cnf_transformation,[],[f84]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1179,plain,
% 7.67/1.44      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1809,plain,
% 7.67/1.44      ( v1_relat_1(sK4) = iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1179,c_1186]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5,plain,
% 7.67/1.44      ( ~ v1_relat_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X1)
% 7.67/1.44      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f55]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1195,plain,
% 7.67/1.44      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2795,plain,
% 7.67/1.44      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1809,c_1195]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3048,plain,
% 7.67/1.44      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1810,c_2795]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_35,negated_conjecture,
% 7.67/1.44      ( v1_funct_1(sK4) ),
% 7.67/1.44      inference(cnf_transformation,[],[f82]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1178,plain,
% 7.67/1.44      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_13,plain,
% 7.67/1.44      ( ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v2_funct_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X0)
% 7.67/1.44      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 7.67/1.44      inference(cnf_transformation,[],[f63]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1189,plain,
% 7.67/1.44      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 7.67/1.44      | v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v2_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3524,plain,
% 7.67/1.44      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1178,c_1189]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_31,negated_conjecture,
% 7.67/1.44      ( v2_funct_1(sK4) ),
% 7.67/1.44      inference(cnf_transformation,[],[f86]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_45,plain,
% 7.67/1.44      ( v2_funct_1(sK4) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3767,plain,
% 7.67/1.44      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_3524,c_45,c_1809]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_12,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.67/1.44      | ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f62]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1190,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.67/1.44      | v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3770,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
% 7.67/1.44      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.67/1.44      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3767,c_1190]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_42,plain,
% 7.67/1.44      ( v1_funct_1(sK4) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_10,plain,
% 7.67/1.44      ( ~ v1_funct_1(X0)
% 7.67/1.44      | v1_funct_1(k2_funct_1(X0))
% 7.67/1.44      | ~ v2_funct_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f60]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2589,plain,
% 7.67/1.44      ( v1_funct_1(k2_funct_1(sK4))
% 7.67/1.44      | ~ v1_funct_1(sK4)
% 7.67/1.44      | ~ v2_funct_1(sK4)
% 7.67/1.44      | ~ v1_relat_1(sK4) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_10]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2590,plain,
% 7.67/1.44      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 7.67/1.44      | v1_funct_1(sK4) != iProver_top
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_2589]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4151,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
% 7.67/1.44      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_3770,c_42,c_45,c_1809,c_2590]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4158,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top
% 7.67/1.44      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_3048,c_4151]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_11,plain,
% 7.67/1.44      ( ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v2_funct_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X0)
% 7.67/1.44      | v1_relat_1(k2_funct_1(X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f59]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_7618,plain,
% 7.67/1.44      ( ~ v1_funct_1(sK4)
% 7.67/1.44      | ~ v2_funct_1(sK4)
% 7.67/1.44      | v1_relat_1(k2_funct_1(sK4))
% 7.67/1.44      | ~ v1_relat_1(sK4) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_11]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_7619,plain,
% 7.67/1.44      ( v1_funct_1(sK4) != iProver_top
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_7618]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_15796,plain,
% 7.67/1.44      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_4158,c_42,c_45,c_1809,c_7619]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_26,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.67/1.44      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.67/1.44      | ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v1_funct_1(X3) ),
% 7.67/1.44      inference(cnf_transformation,[],[f77]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1183,plain,
% 7.67/1.44      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.44      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.67/1.44      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.67/1.44      | v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_funct_1(X3) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_19,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f69]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1184,plain,
% 7.67/1.44      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2708,plain,
% 7.67/1.44      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 7.67/1.44      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.67/1.44      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.67/1.44      | v1_funct_1(X5) != iProver_top
% 7.67/1.44      | v1_funct_1(X4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1183,c_1184]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5384,plain,
% 7.67/1.44      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | v1_funct_1(X2) != iProver_top
% 7.67/1.44      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1179,c_2708]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5689,plain,
% 7.67/1.44      ( v1_funct_1(X2) != iProver_top
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_5384,c_42]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5690,plain,
% 7.67/1.44      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | v1_funct_1(X2) != iProver_top ),
% 7.67/1.44      inference(renaming,[status(thm)],[c_5689]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5697,plain,
% 7.67/1.44      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 7.67/1.44      | v1_funct_1(sK3) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1177,c_5690]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_28,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.67/1.44      | ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v1_funct_1(X3)
% 7.67/1.44      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f78]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1181,plain,
% 7.67/1.44      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.67/1.44      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.67/1.44      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | v1_funct_1(X5) != iProver_top
% 7.67/1.44      | v1_funct_1(X4) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4369,plain,
% 7.67/1.44      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | v1_funct_1(X2) != iProver_top
% 7.67/1.44      | v1_funct_1(sK4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1179,c_1181]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4429,plain,
% 7.67/1.44      ( v1_funct_1(X2) != iProver_top
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_4369,c_42]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4430,plain,
% 7.67/1.44      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.67/1.44      | v1_funct_1(X2) != iProver_top ),
% 7.67/1.44      inference(renaming,[status(thm)],[c_4429]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4437,plain,
% 7.67/1.44      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.67/1.44      | v1_funct_1(sK3) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1177,c_4430]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_38,negated_conjecture,
% 7.67/1.44      ( v1_funct_1(sK3) ),
% 7.67/1.44      inference(cnf_transformation,[],[f79]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_39,plain,
% 7.67/1.44      ( v1_funct_1(sK3) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4510,plain,
% 7.67/1.44      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_4437,c_39]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_32,negated_conjecture,
% 7.67/1.44      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 7.67/1.44      inference(cnf_transformation,[],[f85]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4512,plain,
% 7.67/1.44      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_4510,c_32]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5701,plain,
% 7.67/1.44      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 7.67/1.44      | v1_funct_1(sK3) != iProver_top ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_5697,c_4510,c_4512]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5710,plain,
% 7.67/1.44      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_5701,c_39]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1191,plain,
% 7.67/1.44      ( v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v2_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2918,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 7.67/1.44      | v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v2_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1191,c_1195]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8059,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1178,c_2918]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8594,plain,
% 7.67/1.44      ( v1_relat_1(X0) != iProver_top
% 7.67/1.44      | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_8059,c_45,c_1809]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8595,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(renaming,[status(thm)],[c_8594]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8601,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1809,c_8595]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_15,plain,
% 7.67/1.44      ( ~ v1_funct_1(X0)
% 7.67/1.44      | ~ v2_funct_1(X0)
% 7.67/1.44      | ~ v1_relat_1(X0)
% 7.67/1.44      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 7.67/1.44      inference(cnf_transformation,[],[f64]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1187,plain,
% 7.67/1.44      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 7.67/1.44      | v1_funct_1(X0) != iProver_top
% 7.67/1.44      | v2_funct_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3276,plain,
% 7.67/1.44      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1178,c_1187]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_18,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f68]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1185,plain,
% 7.67/1.44      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.67/1.44      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2037,plain,
% 7.67/1.44      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1179,c_1185]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_25,plain,
% 7.67/1.44      ( ~ v1_funct_2(X0,X1,X2)
% 7.67/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.44      | k1_xboole_0 = X2 ),
% 7.67/1.44      inference(cnf_transformation,[],[f70]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_34,negated_conjecture,
% 7.67/1.44      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.67/1.44      inference(cnf_transformation,[],[f83]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_481,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | k1_relset_1(X1,X2,X0) = X1
% 7.67/1.44      | sK4 != X0
% 7.67/1.44      | sK2 != X2
% 7.67/1.44      | sK1 != X1
% 7.67/1.44      | k1_xboole_0 = X2 ),
% 7.67/1.44      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_482,plain,
% 7.67/1.44      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.67/1.44      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.67/1.44      | k1_xboole_0 = sK2 ),
% 7.67/1.44      inference(unflattening,[status(thm)],[c_481]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_30,negated_conjecture,
% 7.67/1.44      ( k1_xboole_0 != sK2 ),
% 7.67/1.44      inference(cnf_transformation,[],[f87]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_484,plain,
% 7.67/1.44      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_482,c_33,c_30]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2039,plain,
% 7.67/1.44      ( k1_relat_1(sK4) = sK1 ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_2037,c_484]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3278,plain,
% 7.67/1.44      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1)
% 7.67/1.44      | v2_funct_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_3276,c_2039]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_3870,plain,
% 7.67/1.44      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_3278,c_45,c_1809]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_6,plain,
% 7.67/1.44      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 7.67/1.44      | ~ v1_relat_1(X1)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f56]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1194,plain,
% 7.67/1.44      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 7.67/1.44      | v1_relat_1(X0) != iProver_top
% 7.67/1.44      | v1_relat_1(X1) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5714,plain,
% 7.67/1.44      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 7.67/1.44      | v1_relat_1(sK4) != iProver_top
% 7.67/1.44      | v1_relat_1(sK3) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_5710,c_1194]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5961,plain,
% 7.67/1.44      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_5714,c_1809,c_1810]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_4,plain,
% 7.67/1.44      ( ~ v5_relat_1(X0,X1)
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),X1)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(cnf_transformation,[],[f53]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_17,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | v5_relat_1(X0,X2) ),
% 7.67/1.44      inference(cnf_transformation,[],[f67]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_386,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | r1_tarski(k2_relat_1(X3),X4)
% 7.67/1.44      | ~ v1_relat_1(X3)
% 7.67/1.44      | X0 != X3
% 7.67/1.44      | X2 != X4 ),
% 7.67/1.44      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_387,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),X2)
% 7.67/1.44      | ~ v1_relat_1(X0) ),
% 7.67/1.44      inference(unflattening,[status(thm)],[c_386]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_391,plain,
% 7.67/1.44      ( r1_tarski(k2_relat_1(X0),X2)
% 7.67/1.44      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.67/1.44      inference(global_propositional_subsumption,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_387,c_16]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_392,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.67/1.44      inference(renaming,[status(thm)],[c_391]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1175,plain,
% 7.67/1.44      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_392]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1901,plain,
% 7.67/1.44      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1179,c_1175]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_0,plain,
% 7.67/1.44      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.67/1.44      inference(cnf_transformation,[],[f52]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1197,plain,
% 7.67/1.44      ( X0 = X1
% 7.67/1.44      | r1_tarski(X0,X1) != iProver_top
% 7.67/1.44      | r1_tarski(X1,X0) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2206,plain,
% 7.67/1.44      ( k2_relat_1(sK4) = sK2
% 7.67/1.44      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1901,c_1197]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_5966,plain,
% 7.67/1.44      ( k2_relat_1(sK4) = sK2 ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_5961,c_2206]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8608,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(k6_relat_1(sK1)) ),
% 7.67/1.44      inference(light_normalisation,[status(thm)],[c_8601,c_3870,c_5966]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_7,plain,
% 7.67/1.44      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.67/1.44      inference(cnf_transformation,[],[f58]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_8609,plain,
% 7.67/1.44      ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
% 7.67/1.44      inference(demodulation,[status(thm)],[c_8608,c_7]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_15800,plain,
% 7.67/1.44      ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
% 7.67/1.44      inference(light_normalisation,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_15796,c_5710,c_8609]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_2035,plain,
% 7.67/1.44      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.67/1.44      inference(superposition,[status(thm)],[c_1177,c_1184]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_708,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1237,plain,
% 7.67/1.44      ( k2_relset_1(sK0,sK1,sK3) != X0
% 7.67/1.44      | k2_relset_1(sK0,sK1,sK3) = sK1
% 7.67/1.44      | sK1 != X0 ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_708]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1798,plain,
% 7.67/1.44      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 7.67/1.44      | k2_relset_1(sK0,sK1,sK3) = sK1
% 7.67/1.44      | sK1 != k2_relat_1(sK3) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_1237]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1264,plain,
% 7.67/1.44      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_0]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1314,plain,
% 7.67/1.44      ( ~ r1_tarski(k2_relat_1(X0),sK1)
% 7.67/1.44      | ~ r1_tarski(sK1,k2_relat_1(X0))
% 7.67/1.44      | sK1 = k2_relat_1(X0) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_1264]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1668,plain,
% 7.67/1.44      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 7.67/1.44      | ~ r1_tarski(sK1,k2_relat_1(sK3))
% 7.67/1.44      | sK1 = k2_relat_1(sK3) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_1314]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1669,plain,
% 7.67/1.44      ( sK1 = k2_relat_1(sK3)
% 7.67/1.44      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 7.67/1.44      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_1668]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1411,plain,
% 7.67/1.44      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.67/1.44      | r1_tarski(k2_relat_1(X0),sK1) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_392]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1561,plain,
% 7.67/1.44      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.67/1.44      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 7.67/1.44      inference(instantiation,[status(thm)],[c_1411]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_1562,plain,
% 7.67/1.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.67/1.44      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_29,negated_conjecture,
% 7.67/1.44      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 7.67/1.44      inference(cnf_transformation,[],[f88]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(c_41,plain,
% 7.67/1.44      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.67/1.44      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.67/1.44  
% 7.67/1.44  cnf(contradiction,plain,
% 7.67/1.44      ( $false ),
% 7.67/1.44      inference(minisat,
% 7.67/1.44                [status(thm)],
% 7.67/1.44                [c_15800,c_2035,c_1798,c_1669,c_1562,c_29,c_41]) ).
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  % SZS output end CNFRefutation for theBenchmark.p
% 7.67/1.44  
% 7.67/1.44  ------                               Statistics
% 7.67/1.44  
% 7.67/1.44  ------ General
% 7.67/1.44  
% 7.67/1.44  abstr_ref_over_cycles:                  0
% 7.67/1.44  abstr_ref_under_cycles:                 0
% 7.67/1.44  gc_basic_clause_elim:                   0
% 7.67/1.44  forced_gc_time:                         0
% 7.67/1.44  parsing_time:                           0.008
% 7.67/1.44  unif_index_cands_time:                  0.
% 7.67/1.44  unif_index_add_time:                    0.
% 7.67/1.44  orderings_time:                         0.
% 7.67/1.44  out_proof_time:                         0.013
% 7.67/1.44  total_time:                             0.517
% 7.67/1.44  num_of_symbols:                         56
% 7.67/1.44  num_of_terms:                           13737
% 7.67/1.44  
% 7.67/1.44  ------ Preprocessing
% 7.67/1.44  
% 7.67/1.44  num_of_splits:                          0
% 7.67/1.44  num_of_split_atoms:                     0
% 7.67/1.44  num_of_reused_defs:                     0
% 7.67/1.44  num_eq_ax_congr_red:                    13
% 7.67/1.44  num_of_sem_filtered_clauses:            1
% 7.67/1.44  num_of_subtypes:                        0
% 7.67/1.44  monotx_restored_types:                  0
% 7.67/1.44  sat_num_of_epr_types:                   0
% 7.67/1.44  sat_num_of_non_cyclic_types:            0
% 7.67/1.44  sat_guarded_non_collapsed_types:        0
% 7.67/1.44  num_pure_diseq_elim:                    0
% 7.67/1.44  simp_replaced_by:                       0
% 7.67/1.44  res_preprocessed:                       177
% 7.67/1.44  prep_upred:                             0
% 7.67/1.44  prep_unflattend:                        36
% 7.67/1.44  smt_new_axioms:                         0
% 7.67/1.44  pred_elim_cands:                        5
% 7.67/1.44  pred_elim:                              2
% 7.67/1.44  pred_elim_cl:                           4
% 7.67/1.44  pred_elim_cycles:                       4
% 7.67/1.44  merged_defs:                            0
% 7.67/1.44  merged_defs_ncl:                        0
% 7.67/1.44  bin_hyper_res:                          0
% 7.67/1.44  prep_cycles:                            4
% 7.67/1.44  pred_elim_time:                         0.003
% 7.67/1.44  splitting_time:                         0.
% 7.67/1.44  sem_filter_time:                        0.
% 7.67/1.44  monotx_time:                            0.
% 7.67/1.44  subtype_inf_time:                       0.
% 7.67/1.44  
% 7.67/1.44  ------ Problem properties
% 7.67/1.44  
% 7.67/1.44  clauses:                                34
% 7.67/1.44  conjectures:                            8
% 7.67/1.44  epr:                                    6
% 7.67/1.44  horn:                                   31
% 7.67/1.44  ground:                                 14
% 7.67/1.44  unary:                                  12
% 7.67/1.44  binary:                                 5
% 7.67/1.44  lits:                                   87
% 7.67/1.44  lits_eq:                                26
% 7.67/1.44  fd_pure:                                0
% 7.67/1.44  fd_pseudo:                              0
% 7.67/1.44  fd_cond:                                0
% 7.67/1.44  fd_pseudo_cond:                         1
% 7.67/1.44  ac_symbols:                             0
% 7.67/1.44  
% 7.67/1.44  ------ Propositional Solver
% 7.67/1.44  
% 7.67/1.44  prop_solver_calls:                      31
% 7.67/1.44  prop_fast_solver_calls:                 1804
% 7.67/1.44  smt_solver_calls:                       0
% 7.67/1.44  smt_fast_solver_calls:                  0
% 7.67/1.44  prop_num_of_clauses:                    7091
% 7.67/1.44  prop_preprocess_simplified:             15920
% 7.67/1.44  prop_fo_subsumed:                       181
% 7.67/1.44  prop_solver_time:                       0.
% 7.67/1.44  smt_solver_time:                        0.
% 7.67/1.44  smt_fast_solver_time:                   0.
% 7.67/1.44  prop_fast_solver_time:                  0.
% 7.67/1.44  prop_unsat_core_time:                   0.
% 7.67/1.44  
% 7.67/1.44  ------ QBF
% 7.67/1.44  
% 7.67/1.44  qbf_q_res:                              0
% 7.67/1.44  qbf_num_tautologies:                    0
% 7.67/1.44  qbf_prep_cycles:                        0
% 7.67/1.44  
% 7.67/1.44  ------ BMC1
% 7.67/1.44  
% 7.67/1.44  bmc1_current_bound:                     -1
% 7.67/1.44  bmc1_last_solved_bound:                 -1
% 7.67/1.44  bmc1_unsat_core_size:                   -1
% 7.67/1.44  bmc1_unsat_core_parents_size:           -1
% 7.67/1.44  bmc1_merge_next_fun:                    0
% 7.67/1.44  bmc1_unsat_core_clauses_time:           0.
% 7.67/1.44  
% 7.67/1.44  ------ Instantiation
% 7.67/1.44  
% 7.67/1.44  inst_num_of_clauses:                    2176
% 7.67/1.44  inst_num_in_passive:                    1129
% 7.67/1.44  inst_num_in_active:                     971
% 7.67/1.44  inst_num_in_unprocessed:                76
% 7.67/1.44  inst_num_of_loops:                      1120
% 7.67/1.44  inst_num_of_learning_restarts:          0
% 7.67/1.44  inst_num_moves_active_passive:          146
% 7.67/1.44  inst_lit_activity:                      0
% 7.67/1.44  inst_lit_activity_moves:                0
% 7.67/1.44  inst_num_tautologies:                   0
% 7.67/1.44  inst_num_prop_implied:                  0
% 7.67/1.44  inst_num_existing_simplified:           0
% 7.67/1.44  inst_num_eq_res_simplified:             0
% 7.67/1.44  inst_num_child_elim:                    0
% 7.67/1.44  inst_num_of_dismatching_blockings:      782
% 7.67/1.44  inst_num_of_non_proper_insts:           2697
% 7.67/1.44  inst_num_of_duplicates:                 0
% 7.67/1.44  inst_inst_num_from_inst_to_res:         0
% 7.67/1.44  inst_dismatching_checking_time:         0.
% 7.67/1.44  
% 7.67/1.44  ------ Resolution
% 7.67/1.44  
% 7.67/1.44  res_num_of_clauses:                     0
% 7.67/1.44  res_num_in_passive:                     0
% 7.67/1.44  res_num_in_active:                      0
% 7.67/1.44  res_num_of_loops:                       181
% 7.67/1.44  res_forward_subset_subsumed:            270
% 7.67/1.44  res_backward_subset_subsumed:           0
% 7.67/1.44  res_forward_subsumed:                   0
% 7.67/1.44  res_backward_subsumed:                  0
% 7.67/1.44  res_forward_subsumption_resolution:     0
% 7.67/1.44  res_backward_subsumption_resolution:    0
% 7.67/1.44  res_clause_to_clause_subsumption:       1258
% 7.67/1.44  res_orphan_elimination:                 0
% 7.67/1.44  res_tautology_del:                      223
% 7.67/1.44  res_num_eq_res_simplified:              0
% 7.67/1.44  res_num_sel_changes:                    0
% 7.67/1.44  res_moves_from_active_to_pass:          0
% 7.67/1.44  
% 7.67/1.44  ------ Superposition
% 7.67/1.44  
% 7.67/1.44  sup_time_total:                         0.
% 7.67/1.44  sup_time_generating:                    0.
% 7.67/1.44  sup_time_sim_full:                      0.
% 7.67/1.44  sup_time_sim_immed:                     0.
% 7.67/1.44  
% 7.67/1.44  sup_num_of_clauses:                     495
% 7.67/1.44  sup_num_in_active:                      209
% 7.67/1.44  sup_num_in_passive:                     286
% 7.67/1.44  sup_num_of_loops:                       223
% 7.67/1.44  sup_fw_superposition:                   380
% 7.67/1.44  sup_bw_superposition:                   175
% 7.67/1.44  sup_immediate_simplified:               227
% 7.67/1.44  sup_given_eliminated:                   1
% 7.67/1.44  comparisons_done:                       0
% 7.67/1.44  comparisons_avoided:                    3
% 7.67/1.44  
% 7.67/1.44  ------ Simplifications
% 7.67/1.44  
% 7.67/1.44  
% 7.67/1.44  sim_fw_subset_subsumed:                 5
% 7.67/1.44  sim_bw_subset_subsumed:                 27
% 7.67/1.44  sim_fw_subsumed:                        21
% 7.67/1.44  sim_bw_subsumed:                        0
% 7.67/1.44  sim_fw_subsumption_res:                 0
% 7.67/1.44  sim_bw_subsumption_res:                 0
% 7.67/1.44  sim_tautology_del:                      0
% 7.67/1.44  sim_eq_tautology_del:                   34
% 7.67/1.44  sim_eq_res_simp:                        0
% 7.67/1.44  sim_fw_demodulated:                     17
% 7.67/1.44  sim_bw_demodulated:                     6
% 7.67/1.44  sim_light_normalised:                   218
% 7.67/1.44  sim_joinable_taut:                      0
% 7.67/1.44  sim_joinable_simp:                      0
% 7.67/1.44  sim_ac_normalised:                      0
% 7.67/1.44  sim_smt_subsumption:                    0
% 7.67/1.44  
%------------------------------------------------------------------------------
