%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:37 EST 2020

% Result     : Theorem 4.10s
% Output     : CNFRefutation 4.10s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 821 expanded)
%              Number of clauses        :  113 ( 258 expanded)
%              Number of leaves         :   19 ( 199 expanded)
%              Depth                    :   22
%              Number of atoms          :  578 (5523 expanded)
%              Number of equality atoms :  251 (1826 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f40])).

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f47,f46])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f48])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f48])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

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
    inference(flattening,[],[f34])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f83,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f84,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1177,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1521,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1185])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1179,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1520,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1185])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1190,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2553,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1520,c_1190])).

cnf(c_3352,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1521,c_2553])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_419,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_420,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_419])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_424,plain,
    ( ~ v1_relat_1(sK4)
    | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_32])).

cnf(c_1172,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_424])).

cnf(c_1244,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1311,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1244])).

cnf(c_1886,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1172,c_32,c_30,c_420,c_1311])).

cnf(c_9,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1186,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2042,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1886,c_1186])).

cnf(c_3447,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3352,c_2042])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1312,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1311])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2576,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2577,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2576])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2582,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2583,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2582])).

cnf(c_12213,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3447,c_39,c_41,c_1312,c_2577,c_2583])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1180,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2730,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1180])).

cnf(c_2821,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_39])).

cnf(c_2822,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2821])).

cnf(c_2828,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_2822])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2914,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2828,c_36])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1182,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3158,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2914,c_1182])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_5327,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3158,c_36,c_38,c_39,c_41])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1183,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_5334,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_5327,c_1183])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2916,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_2914,c_29])).

cnf(c_5338,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_5334,c_2916])).

cnf(c_1178,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1187,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2552,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1190])).

cnf(c_5535,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1178,c_2552])).

cnf(c_5629,plain,
    ( v1_relat_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5535,c_41,c_1312])).

cnf(c_5630,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5629])).

cnf(c_5636,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_1520,c_5630])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_405,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_406,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_408,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_406,c_32])).

cnf(c_1173,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_2089,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1173,c_32,c_30,c_406,c_1311])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1184,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1581,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1179,c_1184])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_520,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_521,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_523,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_30,c_27])).

cnf(c_1583,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1581,c_523])).

cnf(c_2091,plain,
    ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2089,c_1583])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1189,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5348,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5338,c_1189])).

cnf(c_1461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1462,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_5481,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5348,c_38,c_41,c_1312,c_1462])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_370,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_14])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_370])).

cnf(c_375,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_371,c_13])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_375])).

cnf(c_1175,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_376])).

cnf(c_2491,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1179,c_1175])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1192,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2739,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2491,c_1192])).

cnf(c_5486,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_5481,c_2739])).

cnf(c_5642,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_5636,c_2091,c_5486])).

cnf(c_12217,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12213,c_5338,c_5642])).

cnf(c_737,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1232,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_737])).

cnf(c_1965,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1273,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1335,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(X0))
    | sK1 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_1719,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | sK1 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_1720,plain,
    ( sK1 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1719])).

cnf(c_1423,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | r1_tarski(k2_relat_1(X0),sK1) ),
    inference(instantiation,[status(thm)],[c_376])).

cnf(c_1634,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1423])).

cnf(c_1635,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1634])).

cnf(c_1526,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1177,c_1183])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f84])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12217,c_1965,c_1720,c_1635,c_1526,c_26,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 18:52:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 4.10/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.10/0.98  
% 4.10/0.98  ------  iProver source info
% 4.10/0.98  
% 4.10/0.98  git: date: 2020-06-30 10:37:57 +0100
% 4.10/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.10/0.98  git: non_committed_changes: false
% 4.10/0.98  git: last_make_outside_of_git: false
% 4.10/0.98  
% 4.10/0.98  ------ 
% 4.10/0.98  
% 4.10/0.98  ------ Input Options
% 4.10/0.98  
% 4.10/0.98  --out_options                           all
% 4.10/0.98  --tptp_safe_out                         true
% 4.10/0.98  --problem_path                          ""
% 4.10/0.98  --include_path                          ""
% 4.10/0.98  --clausifier                            res/vclausify_rel
% 4.10/0.98  --clausifier_options                    ""
% 4.10/0.98  --stdin                                 false
% 4.10/0.98  --stats_out                             all
% 4.10/0.98  
% 4.10/0.98  ------ General Options
% 4.10/0.98  
% 4.10/0.98  --fof                                   false
% 4.10/0.98  --time_out_real                         305.
% 4.10/0.98  --time_out_virtual                      -1.
% 4.10/0.98  --symbol_type_check                     false
% 4.10/0.98  --clausify_out                          false
% 4.10/0.98  --sig_cnt_out                           false
% 4.10/0.98  --trig_cnt_out                          false
% 4.10/0.98  --trig_cnt_out_tolerance                1.
% 4.10/0.98  --trig_cnt_out_sk_spl                   false
% 4.10/0.98  --abstr_cl_out                          false
% 4.10/0.98  
% 4.10/0.98  ------ Global Options
% 4.10/0.98  
% 4.10/0.98  --schedule                              default
% 4.10/0.98  --add_important_lit                     false
% 4.10/0.98  --prop_solver_per_cl                    1000
% 4.10/0.98  --min_unsat_core                        false
% 4.10/0.98  --soft_assumptions                      false
% 4.10/0.98  --soft_lemma_size                       3
% 4.10/0.98  --prop_impl_unit_size                   0
% 4.10/0.98  --prop_impl_unit                        []
% 4.10/0.98  --share_sel_clauses                     true
% 4.10/0.98  --reset_solvers                         false
% 4.10/0.98  --bc_imp_inh                            [conj_cone]
% 4.10/0.98  --conj_cone_tolerance                   3.
% 4.10/0.98  --extra_neg_conj                        none
% 4.10/0.98  --large_theory_mode                     true
% 4.10/0.98  --prolific_symb_bound                   200
% 4.10/0.98  --lt_threshold                          2000
% 4.10/0.98  --clause_weak_htbl                      true
% 4.10/0.98  --gc_record_bc_elim                     false
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing Options
% 4.10/0.98  
% 4.10/0.98  --preprocessing_flag                    true
% 4.10/0.98  --time_out_prep_mult                    0.1
% 4.10/0.98  --splitting_mode                        input
% 4.10/0.98  --splitting_grd                         true
% 4.10/0.98  --splitting_cvd                         false
% 4.10/0.98  --splitting_cvd_svl                     false
% 4.10/0.98  --splitting_nvd                         32
% 4.10/0.98  --sub_typing                            true
% 4.10/0.98  --prep_gs_sim                           true
% 4.10/0.98  --prep_unflatten                        true
% 4.10/0.98  --prep_res_sim                          true
% 4.10/0.98  --prep_upred                            true
% 4.10/0.98  --prep_sem_filter                       exhaustive
% 4.10/0.98  --prep_sem_filter_out                   false
% 4.10/0.98  --pred_elim                             true
% 4.10/0.98  --res_sim_input                         true
% 4.10/0.98  --eq_ax_congr_red                       true
% 4.10/0.98  --pure_diseq_elim                       true
% 4.10/0.98  --brand_transform                       false
% 4.10/0.98  --non_eq_to_eq                          false
% 4.10/0.98  --prep_def_merge                        true
% 4.10/0.98  --prep_def_merge_prop_impl              false
% 4.10/0.98  --prep_def_merge_mbd                    true
% 4.10/0.98  --prep_def_merge_tr_red                 false
% 4.10/0.98  --prep_def_merge_tr_cl                  false
% 4.10/0.98  --smt_preprocessing                     true
% 4.10/0.98  --smt_ac_axioms                         fast
% 4.10/0.98  --preprocessed_out                      false
% 4.10/0.98  --preprocessed_stats                    false
% 4.10/0.98  
% 4.10/0.98  ------ Abstraction refinement Options
% 4.10/0.98  
% 4.10/0.98  --abstr_ref                             []
% 4.10/0.98  --abstr_ref_prep                        false
% 4.10/0.98  --abstr_ref_until_sat                   false
% 4.10/0.98  --abstr_ref_sig_restrict                funpre
% 4.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/0.98  --abstr_ref_under                       []
% 4.10/0.98  
% 4.10/0.98  ------ SAT Options
% 4.10/0.98  
% 4.10/0.98  --sat_mode                              false
% 4.10/0.98  --sat_fm_restart_options                ""
% 4.10/0.98  --sat_gr_def                            false
% 4.10/0.98  --sat_epr_types                         true
% 4.10/0.98  --sat_non_cyclic_types                  false
% 4.10/0.98  --sat_finite_models                     false
% 4.10/0.98  --sat_fm_lemmas                         false
% 4.10/0.98  --sat_fm_prep                           false
% 4.10/0.98  --sat_fm_uc_incr                        true
% 4.10/0.98  --sat_out_model                         small
% 4.10/0.98  --sat_out_clauses                       false
% 4.10/0.98  
% 4.10/0.98  ------ QBF Options
% 4.10/0.98  
% 4.10/0.98  --qbf_mode                              false
% 4.10/0.98  --qbf_elim_univ                         false
% 4.10/0.98  --qbf_dom_inst                          none
% 4.10/0.98  --qbf_dom_pre_inst                      false
% 4.10/0.98  --qbf_sk_in                             false
% 4.10/0.98  --qbf_pred_elim                         true
% 4.10/0.98  --qbf_split                             512
% 4.10/0.98  
% 4.10/0.98  ------ BMC1 Options
% 4.10/0.98  
% 4.10/0.98  --bmc1_incremental                      false
% 4.10/0.98  --bmc1_axioms                           reachable_all
% 4.10/0.98  --bmc1_min_bound                        0
% 4.10/0.98  --bmc1_max_bound                        -1
% 4.10/0.98  --bmc1_max_bound_default                -1
% 4.10/0.98  --bmc1_symbol_reachability              true
% 4.10/0.98  --bmc1_property_lemmas                  false
% 4.10/0.98  --bmc1_k_induction                      false
% 4.10/0.98  --bmc1_non_equiv_states                 false
% 4.10/0.98  --bmc1_deadlock                         false
% 4.10/0.98  --bmc1_ucm                              false
% 4.10/0.98  --bmc1_add_unsat_core                   none
% 4.10/0.98  --bmc1_unsat_core_children              false
% 4.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/0.98  --bmc1_out_stat                         full
% 4.10/0.98  --bmc1_ground_init                      false
% 4.10/0.98  --bmc1_pre_inst_next_state              false
% 4.10/0.98  --bmc1_pre_inst_state                   false
% 4.10/0.98  --bmc1_pre_inst_reach_state             false
% 4.10/0.98  --bmc1_out_unsat_core                   false
% 4.10/0.98  --bmc1_aig_witness_out                  false
% 4.10/0.98  --bmc1_verbose                          false
% 4.10/0.98  --bmc1_dump_clauses_tptp                false
% 4.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.10/0.98  --bmc1_dump_file                        -
% 4.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.10/0.98  --bmc1_ucm_extend_mode                  1
% 4.10/0.98  --bmc1_ucm_init_mode                    2
% 4.10/0.98  --bmc1_ucm_cone_mode                    none
% 4.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.10/0.98  --bmc1_ucm_relax_model                  4
% 4.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/0.98  --bmc1_ucm_layered_model                none
% 4.10/0.98  --bmc1_ucm_max_lemma_size               10
% 4.10/0.98  
% 4.10/0.98  ------ AIG Options
% 4.10/0.98  
% 4.10/0.98  --aig_mode                              false
% 4.10/0.98  
% 4.10/0.98  ------ Instantiation Options
% 4.10/0.98  
% 4.10/0.98  --instantiation_flag                    true
% 4.10/0.98  --inst_sos_flag                         true
% 4.10/0.98  --inst_sos_phase                        true
% 4.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel_side                     num_symb
% 4.10/0.98  --inst_solver_per_active                1400
% 4.10/0.98  --inst_solver_calls_frac                1.
% 4.10/0.98  --inst_passive_queue_type               priority_queues
% 4.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/0.98  --inst_passive_queues_freq              [25;2]
% 4.10/0.98  --inst_dismatching                      true
% 4.10/0.98  --inst_eager_unprocessed_to_passive     true
% 4.10/0.98  --inst_prop_sim_given                   true
% 4.10/0.98  --inst_prop_sim_new                     false
% 4.10/0.98  --inst_subs_new                         false
% 4.10/0.98  --inst_eq_res_simp                      false
% 4.10/0.98  --inst_subs_given                       false
% 4.10/0.98  --inst_orphan_elimination               true
% 4.10/0.98  --inst_learning_loop_flag               true
% 4.10/0.98  --inst_learning_start                   3000
% 4.10/0.98  --inst_learning_factor                  2
% 4.10/0.98  --inst_start_prop_sim_after_learn       3
% 4.10/0.98  --inst_sel_renew                        solver
% 4.10/0.98  --inst_lit_activity_flag                true
% 4.10/0.98  --inst_restr_to_given                   false
% 4.10/0.98  --inst_activity_threshold               500
% 4.10/0.98  --inst_out_proof                        true
% 4.10/0.98  
% 4.10/0.98  ------ Resolution Options
% 4.10/0.98  
% 4.10/0.98  --resolution_flag                       true
% 4.10/0.98  --res_lit_sel                           adaptive
% 4.10/0.98  --res_lit_sel_side                      none
% 4.10/0.98  --res_ordering                          kbo
% 4.10/0.98  --res_to_prop_solver                    active
% 4.10/0.98  --res_prop_simpl_new                    false
% 4.10/0.98  --res_prop_simpl_given                  true
% 4.10/0.98  --res_passive_queue_type                priority_queues
% 4.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/0.98  --res_passive_queues_freq               [15;5]
% 4.10/0.98  --res_forward_subs                      full
% 4.10/0.98  --res_backward_subs                     full
% 4.10/0.98  --res_forward_subs_resolution           true
% 4.10/0.98  --res_backward_subs_resolution          true
% 4.10/0.98  --res_orphan_elimination                true
% 4.10/0.98  --res_time_limit                        2.
% 4.10/0.98  --res_out_proof                         true
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Options
% 4.10/0.98  
% 4.10/0.98  --superposition_flag                    true
% 4.10/0.98  --sup_passive_queue_type                priority_queues
% 4.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.10/0.98  --demod_completeness_check              fast
% 4.10/0.98  --demod_use_ground                      true
% 4.10/0.98  --sup_to_prop_solver                    passive
% 4.10/0.98  --sup_prop_simpl_new                    true
% 4.10/0.98  --sup_prop_simpl_given                  true
% 4.10/0.98  --sup_fun_splitting                     true
% 4.10/0.98  --sup_smt_interval                      50000
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Simplification Setup
% 4.10/0.98  
% 4.10/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_immed_triv                        [TrivRules]
% 4.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_bw_main                     []
% 4.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_input_bw                          []
% 4.10/0.98  
% 4.10/0.98  ------ Combination Options
% 4.10/0.98  
% 4.10/0.98  --comb_res_mult                         3
% 4.10/0.98  --comb_sup_mult                         2
% 4.10/0.98  --comb_inst_mult                        10
% 4.10/0.98  
% 4.10/0.98  ------ Debug Options
% 4.10/0.98  
% 4.10/0.98  --dbg_backtrace                         false
% 4.10/0.98  --dbg_dump_prop_clauses                 false
% 4.10/0.98  --dbg_dump_prop_clauses_file            -
% 4.10/0.98  --dbg_out_stat                          false
% 4.10/0.98  ------ Parsing...
% 4.10/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.10/0.98  ------ Proving...
% 4.10/0.98  ------ Problem Properties 
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  clauses                                 30
% 4.10/0.98  conjectures                             7
% 4.10/0.98  EPR                                     5
% 4.10/0.98  Horn                                    27
% 4.10/0.98  unary                                   9
% 4.10/0.98  binary                                  8
% 4.10/0.98  lits                                    72
% 4.10/0.98  lits eq                                 24
% 4.10/0.98  fd_pure                                 0
% 4.10/0.98  fd_pseudo                               0
% 4.10/0.98  fd_cond                                 0
% 4.10/0.98  fd_pseudo_cond                          1
% 4.10/0.98  AC symbols                              0
% 4.10/0.98  
% 4.10/0.98  ------ Schedule dynamic 5 is on 
% 4.10/0.98  
% 4.10/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ 
% 4.10/0.98  Current options:
% 4.10/0.98  ------ 
% 4.10/0.98  
% 4.10/0.98  ------ Input Options
% 4.10/0.98  
% 4.10/0.98  --out_options                           all
% 4.10/0.98  --tptp_safe_out                         true
% 4.10/0.98  --problem_path                          ""
% 4.10/0.98  --include_path                          ""
% 4.10/0.98  --clausifier                            res/vclausify_rel
% 4.10/0.98  --clausifier_options                    ""
% 4.10/0.98  --stdin                                 false
% 4.10/0.98  --stats_out                             all
% 4.10/0.98  
% 4.10/0.98  ------ General Options
% 4.10/0.98  
% 4.10/0.98  --fof                                   false
% 4.10/0.98  --time_out_real                         305.
% 4.10/0.98  --time_out_virtual                      -1.
% 4.10/0.98  --symbol_type_check                     false
% 4.10/0.98  --clausify_out                          false
% 4.10/0.98  --sig_cnt_out                           false
% 4.10/0.98  --trig_cnt_out                          false
% 4.10/0.98  --trig_cnt_out_tolerance                1.
% 4.10/0.98  --trig_cnt_out_sk_spl                   false
% 4.10/0.98  --abstr_cl_out                          false
% 4.10/0.98  
% 4.10/0.98  ------ Global Options
% 4.10/0.98  
% 4.10/0.98  --schedule                              default
% 4.10/0.98  --add_important_lit                     false
% 4.10/0.98  --prop_solver_per_cl                    1000
% 4.10/0.98  --min_unsat_core                        false
% 4.10/0.98  --soft_assumptions                      false
% 4.10/0.98  --soft_lemma_size                       3
% 4.10/0.98  --prop_impl_unit_size                   0
% 4.10/0.98  --prop_impl_unit                        []
% 4.10/0.98  --share_sel_clauses                     true
% 4.10/0.98  --reset_solvers                         false
% 4.10/0.98  --bc_imp_inh                            [conj_cone]
% 4.10/0.98  --conj_cone_tolerance                   3.
% 4.10/0.98  --extra_neg_conj                        none
% 4.10/0.98  --large_theory_mode                     true
% 4.10/0.98  --prolific_symb_bound                   200
% 4.10/0.98  --lt_threshold                          2000
% 4.10/0.98  --clause_weak_htbl                      true
% 4.10/0.98  --gc_record_bc_elim                     false
% 4.10/0.98  
% 4.10/0.98  ------ Preprocessing Options
% 4.10/0.98  
% 4.10/0.98  --preprocessing_flag                    true
% 4.10/0.98  --time_out_prep_mult                    0.1
% 4.10/0.98  --splitting_mode                        input
% 4.10/0.98  --splitting_grd                         true
% 4.10/0.98  --splitting_cvd                         false
% 4.10/0.98  --splitting_cvd_svl                     false
% 4.10/0.98  --splitting_nvd                         32
% 4.10/0.98  --sub_typing                            true
% 4.10/0.98  --prep_gs_sim                           true
% 4.10/0.98  --prep_unflatten                        true
% 4.10/0.98  --prep_res_sim                          true
% 4.10/0.98  --prep_upred                            true
% 4.10/0.98  --prep_sem_filter                       exhaustive
% 4.10/0.98  --prep_sem_filter_out                   false
% 4.10/0.98  --pred_elim                             true
% 4.10/0.98  --res_sim_input                         true
% 4.10/0.98  --eq_ax_congr_red                       true
% 4.10/0.98  --pure_diseq_elim                       true
% 4.10/0.98  --brand_transform                       false
% 4.10/0.98  --non_eq_to_eq                          false
% 4.10/0.98  --prep_def_merge                        true
% 4.10/0.98  --prep_def_merge_prop_impl              false
% 4.10/0.98  --prep_def_merge_mbd                    true
% 4.10/0.98  --prep_def_merge_tr_red                 false
% 4.10/0.98  --prep_def_merge_tr_cl                  false
% 4.10/0.98  --smt_preprocessing                     true
% 4.10/0.98  --smt_ac_axioms                         fast
% 4.10/0.98  --preprocessed_out                      false
% 4.10/0.98  --preprocessed_stats                    false
% 4.10/0.98  
% 4.10/0.98  ------ Abstraction refinement Options
% 4.10/0.98  
% 4.10/0.98  --abstr_ref                             []
% 4.10/0.98  --abstr_ref_prep                        false
% 4.10/0.98  --abstr_ref_until_sat                   false
% 4.10/0.98  --abstr_ref_sig_restrict                funpre
% 4.10/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 4.10/0.98  --abstr_ref_under                       []
% 4.10/0.98  
% 4.10/0.98  ------ SAT Options
% 4.10/0.98  
% 4.10/0.98  --sat_mode                              false
% 4.10/0.98  --sat_fm_restart_options                ""
% 4.10/0.98  --sat_gr_def                            false
% 4.10/0.98  --sat_epr_types                         true
% 4.10/0.98  --sat_non_cyclic_types                  false
% 4.10/0.98  --sat_finite_models                     false
% 4.10/0.98  --sat_fm_lemmas                         false
% 4.10/0.98  --sat_fm_prep                           false
% 4.10/0.98  --sat_fm_uc_incr                        true
% 4.10/0.98  --sat_out_model                         small
% 4.10/0.98  --sat_out_clauses                       false
% 4.10/0.98  
% 4.10/0.98  ------ QBF Options
% 4.10/0.98  
% 4.10/0.98  --qbf_mode                              false
% 4.10/0.98  --qbf_elim_univ                         false
% 4.10/0.98  --qbf_dom_inst                          none
% 4.10/0.98  --qbf_dom_pre_inst                      false
% 4.10/0.98  --qbf_sk_in                             false
% 4.10/0.98  --qbf_pred_elim                         true
% 4.10/0.98  --qbf_split                             512
% 4.10/0.98  
% 4.10/0.98  ------ BMC1 Options
% 4.10/0.98  
% 4.10/0.98  --bmc1_incremental                      false
% 4.10/0.98  --bmc1_axioms                           reachable_all
% 4.10/0.98  --bmc1_min_bound                        0
% 4.10/0.98  --bmc1_max_bound                        -1
% 4.10/0.98  --bmc1_max_bound_default                -1
% 4.10/0.98  --bmc1_symbol_reachability              true
% 4.10/0.98  --bmc1_property_lemmas                  false
% 4.10/0.98  --bmc1_k_induction                      false
% 4.10/0.98  --bmc1_non_equiv_states                 false
% 4.10/0.98  --bmc1_deadlock                         false
% 4.10/0.98  --bmc1_ucm                              false
% 4.10/0.98  --bmc1_add_unsat_core                   none
% 4.10/0.98  --bmc1_unsat_core_children              false
% 4.10/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 4.10/0.98  --bmc1_out_stat                         full
% 4.10/0.98  --bmc1_ground_init                      false
% 4.10/0.98  --bmc1_pre_inst_next_state              false
% 4.10/0.98  --bmc1_pre_inst_state                   false
% 4.10/0.98  --bmc1_pre_inst_reach_state             false
% 4.10/0.98  --bmc1_out_unsat_core                   false
% 4.10/0.98  --bmc1_aig_witness_out                  false
% 4.10/0.98  --bmc1_verbose                          false
% 4.10/0.98  --bmc1_dump_clauses_tptp                false
% 4.10/0.98  --bmc1_dump_unsat_core_tptp             false
% 4.10/0.98  --bmc1_dump_file                        -
% 4.10/0.98  --bmc1_ucm_expand_uc_limit              128
% 4.10/0.98  --bmc1_ucm_n_expand_iterations          6
% 4.10/0.98  --bmc1_ucm_extend_mode                  1
% 4.10/0.98  --bmc1_ucm_init_mode                    2
% 4.10/0.98  --bmc1_ucm_cone_mode                    none
% 4.10/0.98  --bmc1_ucm_reduced_relation_type        0
% 4.10/0.98  --bmc1_ucm_relax_model                  4
% 4.10/0.98  --bmc1_ucm_full_tr_after_sat            true
% 4.10/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 4.10/0.98  --bmc1_ucm_layered_model                none
% 4.10/0.98  --bmc1_ucm_max_lemma_size               10
% 4.10/0.98  
% 4.10/0.98  ------ AIG Options
% 4.10/0.98  
% 4.10/0.98  --aig_mode                              false
% 4.10/0.98  
% 4.10/0.98  ------ Instantiation Options
% 4.10/0.98  
% 4.10/0.98  --instantiation_flag                    true
% 4.10/0.98  --inst_sos_flag                         true
% 4.10/0.98  --inst_sos_phase                        true
% 4.10/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 4.10/0.98  --inst_lit_sel_side                     none
% 4.10/0.98  --inst_solver_per_active                1400
% 4.10/0.98  --inst_solver_calls_frac                1.
% 4.10/0.98  --inst_passive_queue_type               priority_queues
% 4.10/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 4.10/0.98  --inst_passive_queues_freq              [25;2]
% 4.10/0.98  --inst_dismatching                      true
% 4.10/0.98  --inst_eager_unprocessed_to_passive     true
% 4.10/0.98  --inst_prop_sim_given                   true
% 4.10/0.98  --inst_prop_sim_new                     false
% 4.10/0.98  --inst_subs_new                         false
% 4.10/0.98  --inst_eq_res_simp                      false
% 4.10/0.98  --inst_subs_given                       false
% 4.10/0.98  --inst_orphan_elimination               true
% 4.10/0.98  --inst_learning_loop_flag               true
% 4.10/0.98  --inst_learning_start                   3000
% 4.10/0.98  --inst_learning_factor                  2
% 4.10/0.98  --inst_start_prop_sim_after_learn       3
% 4.10/0.98  --inst_sel_renew                        solver
% 4.10/0.98  --inst_lit_activity_flag                true
% 4.10/0.98  --inst_restr_to_given                   false
% 4.10/0.98  --inst_activity_threshold               500
% 4.10/0.98  --inst_out_proof                        true
% 4.10/0.98  
% 4.10/0.98  ------ Resolution Options
% 4.10/0.98  
% 4.10/0.98  --resolution_flag                       false
% 4.10/0.98  --res_lit_sel                           adaptive
% 4.10/0.98  --res_lit_sel_side                      none
% 4.10/0.98  --res_ordering                          kbo
% 4.10/0.98  --res_to_prop_solver                    active
% 4.10/0.98  --res_prop_simpl_new                    false
% 4.10/0.98  --res_prop_simpl_given                  true
% 4.10/0.98  --res_passive_queue_type                priority_queues
% 4.10/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 4.10/0.98  --res_passive_queues_freq               [15;5]
% 4.10/0.98  --res_forward_subs                      full
% 4.10/0.98  --res_backward_subs                     full
% 4.10/0.98  --res_forward_subs_resolution           true
% 4.10/0.98  --res_backward_subs_resolution          true
% 4.10/0.98  --res_orphan_elimination                true
% 4.10/0.98  --res_time_limit                        2.
% 4.10/0.98  --res_out_proof                         true
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Options
% 4.10/0.98  
% 4.10/0.98  --superposition_flag                    true
% 4.10/0.98  --sup_passive_queue_type                priority_queues
% 4.10/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 4.10/0.98  --sup_passive_queues_freq               [8;1;4]
% 4.10/0.98  --demod_completeness_check              fast
% 4.10/0.98  --demod_use_ground                      true
% 4.10/0.98  --sup_to_prop_solver                    passive
% 4.10/0.98  --sup_prop_simpl_new                    true
% 4.10/0.98  --sup_prop_simpl_given                  true
% 4.10/0.98  --sup_fun_splitting                     true
% 4.10/0.98  --sup_smt_interval                      50000
% 4.10/0.98  
% 4.10/0.98  ------ Superposition Simplification Setup
% 4.10/0.98  
% 4.10/0.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 4.10/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 4.10/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 4.10/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 4.10/0.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_immed_triv                        [TrivRules]
% 4.10/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_immed_bw_main                     []
% 4.10/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 4.10/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 4.10/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 4.10/0.98  --sup_input_bw                          []
% 4.10/0.98  
% 4.10/0.98  ------ Combination Options
% 4.10/0.98  
% 4.10/0.98  --comb_res_mult                         3
% 4.10/0.98  --comb_sup_mult                         2
% 4.10/0.98  --comb_inst_mult                        10
% 4.10/0.98  
% 4.10/0.98  ------ Debug Options
% 4.10/0.98  
% 4.10/0.98  --dbg_backtrace                         false
% 4.10/0.98  --dbg_dump_prop_clauses                 false
% 4.10/0.98  --dbg_dump_prop_clauses_file            -
% 4.10/0.98  --dbg_out_stat                          false
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  ------ Proving...
% 4.10/0.98  
% 4.10/0.98  
% 4.10/0.98  % SZS status Theorem for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 4.10/0.98  
% 4.10/0.98  fof(f16,conjecture,(
% 4.10/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f17,negated_conjecture,(
% 4.10/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 4.10/0.98    inference(negated_conjecture,[],[f16])).
% 4.10/0.98  
% 4.10/0.98  fof(f40,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 4.10/0.98    inference(ennf_transformation,[],[f17])).
% 4.10/0.98  
% 4.10/0.98  fof(f41,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 4.10/0.98    inference(flattening,[],[f40])).
% 4.10/0.98  
% 4.10/0.98  fof(f47,plain,(
% 4.10/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f46,plain,(
% 4.10/0.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 4.10/0.98    introduced(choice_axiom,[])).
% 4.10/0.98  
% 4.10/0.98  fof(f48,plain,(
% 4.10/0.98    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 4.10/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f47,f46])).
% 4.10/0.98  
% 4.10/0.98  fof(f77,plain,(
% 4.10/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f9,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f30,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(ennf_transformation,[],[f9])).
% 4.10/0.98  
% 4.10/0.98  fof(f62,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f30])).
% 4.10/0.98  
% 4.10/0.98  fof(f80,plain,(
% 4.10/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f3,axiom,(
% 4.10/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f20,plain,(
% 4.10/0.98    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.10/0.98    inference(ennf_transformation,[],[f3])).
% 4.10/0.98  
% 4.10/0.98  fof(f54,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f20])).
% 4.10/0.98  
% 4.10/0.98  fof(f7,axiom,(
% 4.10/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f26,plain,(
% 4.10/0.98    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.10/0.98    inference(ennf_transformation,[],[f7])).
% 4.10/0.98  
% 4.10/0.98  fof(f27,plain,(
% 4.10/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.10/0.98    inference(flattening,[],[f26])).
% 4.10/0.98  
% 4.10/0.98  fof(f59,plain,(
% 4.10/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f27])).
% 4.10/0.98  
% 4.10/0.98  fof(f82,plain,(
% 4.10/0.98    v2_funct_1(sK4)),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f78,plain,(
% 4.10/0.98    v1_funct_1(sK4)),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f6,axiom,(
% 4.10/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f24,plain,(
% 4.10/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.10/0.98    inference(ennf_transformation,[],[f6])).
% 4.10/0.98  
% 4.10/0.98  fof(f25,plain,(
% 4.10/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.10/0.98    inference(flattening,[],[f24])).
% 4.10/0.98  
% 4.10/0.98  fof(f58,plain,(
% 4.10/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f25])).
% 4.10/0.98  
% 4.10/0.98  fof(f5,axiom,(
% 4.10/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f22,plain,(
% 4.10/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.10/0.98    inference(ennf_transformation,[],[f5])).
% 4.10/0.98  
% 4.10/0.98  fof(f23,plain,(
% 4.10/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.10/0.98    inference(flattening,[],[f22])).
% 4.10/0.98  
% 4.10/0.98  fof(f57,plain,(
% 4.10/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f23])).
% 4.10/0.98  
% 4.10/0.98  fof(f56,plain,(
% 4.10/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f23])).
% 4.10/0.98  
% 4.10/0.98  fof(f15,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f38,plain,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.10/0.98    inference(ennf_transformation,[],[f15])).
% 4.10/0.98  
% 4.10/0.98  fof(f39,plain,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.10/0.98    inference(flattening,[],[f38])).
% 4.10/0.98  
% 4.10/0.98  fof(f74,plain,(
% 4.10/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f39])).
% 4.10/0.98  
% 4.10/0.98  fof(f75,plain,(
% 4.10/0.98    v1_funct_1(sK3)),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f14,axiom,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f36,plain,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 4.10/0.98    inference(ennf_transformation,[],[f14])).
% 4.10/0.98  
% 4.10/0.98  fof(f37,plain,(
% 4.10/0.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 4.10/0.98    inference(flattening,[],[f36])).
% 4.10/0.98  
% 4.10/0.98  fof(f73,plain,(
% 4.10/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f37])).
% 4.10/0.98  
% 4.10/0.98  fof(f12,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f33,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(ennf_transformation,[],[f12])).
% 4.10/0.98  
% 4.10/0.98  fof(f65,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f33])).
% 4.10/0.98  
% 4.10/0.98  fof(f81,plain,(
% 4.10/0.98    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f8,axiom,(
% 4.10/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f28,plain,(
% 4.10/0.98    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.10/0.98    inference(ennf_transformation,[],[f8])).
% 4.10/0.98  
% 4.10/0.98  fof(f29,plain,(
% 4.10/0.98    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.10/0.98    inference(flattening,[],[f28])).
% 4.10/0.98  
% 4.10/0.98  fof(f61,plain,(
% 4.10/0.98    ( ! [X0] : (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.10/0.98    inference(cnf_transformation,[],[f29])).
% 4.10/0.98  
% 4.10/0.98  fof(f11,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f32,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(ennf_transformation,[],[f11])).
% 4.10/0.98  
% 4.10/0.98  fof(f64,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f32])).
% 4.10/0.98  
% 4.10/0.98  fof(f13,axiom,(
% 4.10/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.10/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.98  
% 4.10/0.98  fof(f34,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(ennf_transformation,[],[f13])).
% 4.10/0.98  
% 4.10/0.98  fof(f35,plain,(
% 4.10/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(flattening,[],[f34])).
% 4.10/0.98  
% 4.10/0.98  fof(f45,plain,(
% 4.10/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.98    inference(nnf_transformation,[],[f35])).
% 4.10/0.98  
% 4.10/0.98  fof(f66,plain,(
% 4.10/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/0.98    inference(cnf_transformation,[],[f45])).
% 4.10/0.98  
% 4.10/0.98  fof(f79,plain,(
% 4.10/0.98    v1_funct_2(sK4,sK1,sK2)),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f83,plain,(
% 4.10/0.98    k1_xboole_0 != sK2),
% 4.10/0.98    inference(cnf_transformation,[],[f48])).
% 4.10/0.98  
% 4.10/0.98  fof(f4,axiom,(
% 4.10/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f21,plain,(
% 4.10/0.99    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 4.10/0.99    inference(ennf_transformation,[],[f4])).
% 4.10/0.99  
% 4.10/0.99  fof(f55,plain,(
% 4.10/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f21])).
% 4.10/0.99  
% 4.10/0.99  fof(f2,axiom,(
% 4.10/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f19,plain,(
% 4.10/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.10/0.99    inference(ennf_transformation,[],[f2])).
% 4.10/0.99  
% 4.10/0.99  fof(f44,plain,(
% 4.10/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.10/0.99    inference(nnf_transformation,[],[f19])).
% 4.10/0.99  
% 4.10/0.99  fof(f52,plain,(
% 4.10/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f44])).
% 4.10/0.99  
% 4.10/0.99  fof(f10,axiom,(
% 4.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f18,plain,(
% 4.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.10/0.99    inference(pure_predicate_removal,[],[f10])).
% 4.10/0.99  
% 4.10/0.99  fof(f31,plain,(
% 4.10/0.99    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.10/0.99    inference(ennf_transformation,[],[f18])).
% 4.10/0.99  
% 4.10/0.99  fof(f63,plain,(
% 4.10/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.10/0.99    inference(cnf_transformation,[],[f31])).
% 4.10/0.99  
% 4.10/0.99  fof(f1,axiom,(
% 4.10/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.10/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.10/0.99  
% 4.10/0.99  fof(f42,plain,(
% 4.10/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.10/0.99    inference(nnf_transformation,[],[f1])).
% 4.10/0.99  
% 4.10/0.99  fof(f43,plain,(
% 4.10/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.10/0.99    inference(flattening,[],[f42])).
% 4.10/0.99  
% 4.10/0.99  fof(f51,plain,(
% 4.10/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.10/0.99    inference(cnf_transformation,[],[f43])).
% 4.10/0.99  
% 4.10/0.99  fof(f84,plain,(
% 4.10/0.99    k2_relset_1(sK0,sK1,sK3) != sK1),
% 4.10/0.99    inference(cnf_transformation,[],[f48])).
% 4.10/0.99  
% 4.10/0.99  cnf(c_33,negated_conjecture,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 4.10/0.99      inference(cnf_transformation,[],[f77]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1177,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_13,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | v1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f62]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1185,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.10/0.99      | v1_relat_1(X0) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1521,plain,
% 4.10/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1177,c_1185]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_30,negated_conjecture,
% 4.10/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 4.10/0.99      inference(cnf_transformation,[],[f80]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1179,plain,
% 4.10/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1520,plain,
% 4.10/0.99      ( v1_relat_1(sK4) = iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1179,c_1185]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5,plain,
% 4.10/0.99      ( ~ v1_relat_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X1)
% 4.10/0.99      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 4.10/0.99      inference(cnf_transformation,[],[f54]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1190,plain,
% 4.10/0.99      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 4.10/0.99      | v1_relat_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2553,plain,
% 4.10/0.99      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 4.10/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1520,c_1190]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3352,plain,
% 4.10/0.99      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1521,c_2553]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_10,plain,
% 4.10/0.99      ( ~ v2_funct_1(X0)
% 4.10/0.99      | ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0)
% 4.10/0.99      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 4.10/0.99      inference(cnf_transformation,[],[f59]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_28,negated_conjecture,
% 4.10/0.99      ( v2_funct_1(sK4) ),
% 4.10/0.99      inference(cnf_transformation,[],[f82]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_419,plain,
% 4.10/0.99      ( ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0)
% 4.10/0.99      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 4.10/0.99      | sK4 != X0 ),
% 4.10/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_420,plain,
% 4.10/0.99      ( ~ v1_funct_1(sK4)
% 4.10/0.99      | ~ v1_relat_1(sK4)
% 4.10/0.99      | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 4.10/0.99      inference(unflattening,[status(thm)],[c_419]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_32,negated_conjecture,
% 4.10/0.99      ( v1_funct_1(sK4) ),
% 4.10/0.99      inference(cnf_transformation,[],[f78]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_424,plain,
% 4.10/0.99      ( ~ v1_relat_1(sK4)
% 4.10/0.99      | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_420,c_32]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1172,plain,
% 4.10/0.99      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_424]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1244,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.10/0.99      | v1_relat_1(sK4) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1311,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 4.10/0.99      | v1_relat_1(sK4) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1244]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1886,plain,
% 4.10/0.99      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_1172,c_32,c_30,c_420,c_1311]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_9,plain,
% 4.10/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 4.10/0.99      | ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f58]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1186,plain,
% 4.10/0.99      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 4.10/0.99      | v1_funct_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2042,plain,
% 4.10/0.99      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
% 4.10/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 4.10/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1886,c_1186]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3447,plain,
% 4.10/0.99      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top
% 4.10/0.99      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 4.10/0.99      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_3352,c_2042]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_39,plain,
% 4.10/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_41,plain,
% 4.10/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1312,plain,
% 4.10/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 4.10/0.99      | v1_relat_1(sK4) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1311]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_7,plain,
% 4.10/0.99      ( ~ v1_funct_1(X0)
% 4.10/0.99      | v1_funct_1(k2_funct_1(X0))
% 4.10/0.99      | ~ v1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f57]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2576,plain,
% 4.10/0.99      ( v1_funct_1(k2_funct_1(sK4))
% 4.10/0.99      | ~ v1_funct_1(sK4)
% 4.10/0.99      | ~ v1_relat_1(sK4) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2577,plain,
% 4.10/0.99      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 4.10/0.99      | v1_funct_1(sK4) != iProver_top
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2576]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_8,plain,
% 4.10/0.99      ( ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0)
% 4.10/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 4.10/0.99      inference(cnf_transformation,[],[f56]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2582,plain,
% 4.10/0.99      ( ~ v1_funct_1(sK4)
% 4.10/0.99      | v1_relat_1(k2_funct_1(sK4))
% 4.10/0.99      | ~ v1_relat_1(sK4) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2583,plain,
% 4.10/0.99      ( v1_funct_1(sK4) != iProver_top
% 4.10/0.99      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2582]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_12213,plain,
% 4.10/0.99      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_3447,c_39,c_41,c_1312,c_2577,c_2583]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_25,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.10/0.99      | ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_funct_1(X3)
% 4.10/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f74]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1180,plain,
% 4.10/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 4.10/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 4.10/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/0.99      | v1_funct_1(X5) != iProver_top
% 4.10/0.99      | v1_funct_1(X4) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2730,plain,
% 4.10/0.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/0.99      | v1_funct_1(X2) != iProver_top
% 4.10/0.99      | v1_funct_1(sK4) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1179,c_1180]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2821,plain,
% 4.10/0.99      ( v1_funct_1(X2) != iProver_top
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/0.99      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_2730,c_39]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2822,plain,
% 4.10/0.99      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.10/0.99      | v1_funct_1(X2) != iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_2821]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2828,plain,
% 4.10/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 4.10/0.99      | v1_funct_1(sK3) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1177,c_2822]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_35,negated_conjecture,
% 4.10/0.99      ( v1_funct_1(sK3) ),
% 4.10/0.99      inference(cnf_transformation,[],[f75]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_36,plain,
% 4.10/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2914,plain,
% 4.10/0.99      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_2828,c_36]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_23,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 4.10/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 4.10/0.99      | ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_funct_1(X3) ),
% 4.10/0.99      inference(cnf_transformation,[],[f73]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1182,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.10/0.99      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 4.10/0.99      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 4.10/0.99      | v1_funct_1(X0) != iProver_top
% 4.10/0.99      | v1_funct_1(X3) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_3158,plain,
% 4.10/0.99      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 4.10/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 4.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/0.99      | v1_funct_1(sK4) != iProver_top
% 4.10/0.99      | v1_funct_1(sK3) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_2914,c_1182]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_38,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5327,plain,
% 4.10/0.99      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_3158,c_36,c_38,c_39,c_41]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_16,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f65]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1183,plain,
% 4.10/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5334,plain,
% 4.10/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_5327,c_1183]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_29,negated_conjecture,
% 4.10/0.99      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 4.10/0.99      inference(cnf_transformation,[],[f81]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2916,plain,
% 4.10/0.99      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 4.10/0.99      inference(demodulation,[status(thm)],[c_2914,c_29]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5338,plain,
% 4.10/0.99      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_5334,c_2916]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1178,plain,
% 4.10/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1187,plain,
% 4.10/0.99      ( v1_funct_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2552,plain,
% 4.10/0.99      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 4.10/0.99      | v1_funct_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1187,c_1190]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5535,plain,
% 4.10/0.99      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 4.10/0.99      | v1_relat_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1178,c_2552]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5629,plain,
% 4.10/0.99      ( v1_relat_1(X0) != iProver_top
% 4.10/0.99      | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_5535,c_41,c_1312]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5630,plain,
% 4.10/0.99      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 4.10/0.99      | v1_relat_1(X0) != iProver_top ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_5629]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5636,plain,
% 4.10/0.99      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1520,c_5630]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_11,plain,
% 4.10/0.99      ( ~ v2_funct_1(X0)
% 4.10/0.99      | ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0)
% 4.10/0.99      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f61]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_405,plain,
% 4.10/0.99      ( ~ v1_funct_1(X0)
% 4.10/0.99      | ~ v1_relat_1(X0)
% 4.10/0.99      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 4.10/0.99      | sK4 != X0 ),
% 4.10/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_406,plain,
% 4.10/0.99      ( ~ v1_funct_1(sK4)
% 4.10/0.99      | ~ v1_relat_1(sK4)
% 4.10/0.99      | k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
% 4.10/0.99      inference(unflattening,[status(thm)],[c_405]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_408,plain,
% 4.10/0.99      ( ~ v1_relat_1(sK4)
% 4.10/0.99      | k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_406,c_32]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1173,plain,
% 4.10/0.99      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4)
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2089,plain,
% 4.10/0.99      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = k1_relat_1(sK4) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_1173,c_32,c_30,c_406,c_1311]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_15,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f64]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1184,plain,
% 4.10/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1581,plain,
% 4.10/0.99      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1179,c_1184]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_22,plain,
% 4.10/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.10/0.99      | k1_xboole_0 = X2 ),
% 4.10/0.99      inference(cnf_transformation,[],[f66]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_31,negated_conjecture,
% 4.10/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 4.10/0.99      inference(cnf_transformation,[],[f79]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_520,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | k1_relset_1(X1,X2,X0) = X1
% 4.10/0.99      | sK4 != X0
% 4.10/0.99      | sK2 != X2
% 4.10/0.99      | sK1 != X1
% 4.10/0.99      | k1_xboole_0 = X2 ),
% 4.10/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_521,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 4.10/0.99      | k1_relset_1(sK1,sK2,sK4) = sK1
% 4.10/0.99      | k1_xboole_0 = sK2 ),
% 4.10/0.99      inference(unflattening,[status(thm)],[c_520]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_27,negated_conjecture,
% 4.10/0.99      ( k1_xboole_0 != sK2 ),
% 4.10/0.99      inference(cnf_transformation,[],[f83]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_523,plain,
% 4.10/0.99      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_521,c_30,c_27]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1583,plain,
% 4.10/0.99      ( k1_relat_1(sK4) = sK1 ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_1581,c_523]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2091,plain,
% 4.10/0.99      ( k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) = sK1 ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_2089,c_1583]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_6,plain,
% 4.10/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 4.10/0.99      | ~ v1_relat_1(X1)
% 4.10/0.99      | ~ v1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f55]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1189,plain,
% 4.10/0.99      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 4.10/0.99      | v1_relat_1(X0) != iProver_top
% 4.10/0.99      | v1_relat_1(X1) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5348,plain,
% 4.10/0.99      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 4.10/0.99      | v1_relat_1(sK4) != iProver_top
% 4.10/0.99      | v1_relat_1(sK3) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_5338,c_1189]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1461,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.10/0.99      | v1_relat_1(sK3) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1462,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/0.99      | v1_relat_1(sK3) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5481,plain,
% 4.10/0.99      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_5348,c_38,c_41,c_1312,c_1462]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_4,plain,
% 4.10/0.99      ( ~ v5_relat_1(X0,X1)
% 4.10/0.99      | r1_tarski(k2_relat_1(X0),X1)
% 4.10/0.99      | ~ v1_relat_1(X0) ),
% 4.10/0.99      inference(cnf_transformation,[],[f52]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_14,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | v5_relat_1(X0,X2) ),
% 4.10/0.99      inference(cnf_transformation,[],[f63]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_370,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | r1_tarski(k2_relat_1(X3),X4)
% 4.10/0.99      | ~ v1_relat_1(X3)
% 4.10/0.99      | X0 != X3
% 4.10/0.99      | X2 != X4 ),
% 4.10/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_14]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_371,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 4.10/0.99      | ~ v1_relat_1(X0) ),
% 4.10/0.99      inference(unflattening,[status(thm)],[c_370]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_375,plain,
% 4.10/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 4.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.10/0.99      inference(global_propositional_subsumption,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_371,c_13]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_376,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.10/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 4.10/0.99      inference(renaming,[status(thm)],[c_375]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1175,plain,
% 4.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.10/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_376]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2491,plain,
% 4.10/0.99      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1179,c_1175]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_0,plain,
% 4.10/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.10/0.99      inference(cnf_transformation,[],[f51]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1192,plain,
% 4.10/0.99      ( X0 = X1
% 4.10/0.99      | r1_tarski(X0,X1) != iProver_top
% 4.10/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_2739,plain,
% 4.10/0.99      ( k2_relat_1(sK4) = sK2
% 4.10/0.99      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_2491,c_1192]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5486,plain,
% 4.10/0.99      ( k2_relat_1(sK4) = sK2 ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_5481,c_2739]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_5642,plain,
% 4.10/0.99      ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
% 4.10/0.99      inference(light_normalisation,[status(thm)],[c_5636,c_2091,c_5486]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_12217,plain,
% 4.10/0.99      ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
% 4.10/0.99      inference(light_normalisation,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_12213,c_5338,c_5642]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_737,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1232,plain,
% 4.10/0.99      ( k2_relset_1(sK0,sK1,sK3) != X0
% 4.10/0.99      | k2_relset_1(sK0,sK1,sK3) = sK1
% 4.10/0.99      | sK1 != X0 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_737]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1965,plain,
% 4.10/0.99      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 4.10/0.99      | k2_relset_1(sK0,sK1,sK3) = sK1
% 4.10/0.99      | sK1 != k2_relat_1(sK3) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1232]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1273,plain,
% 4.10/0.99      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1335,plain,
% 4.10/0.99      ( ~ r1_tarski(k2_relat_1(X0),sK1)
% 4.10/0.99      | ~ r1_tarski(sK1,k2_relat_1(X0))
% 4.10/0.99      | sK1 = k2_relat_1(X0) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1273]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1719,plain,
% 4.10/0.99      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 4.10/0.99      | ~ r1_tarski(sK1,k2_relat_1(sK3))
% 4.10/0.99      | sK1 = k2_relat_1(sK3) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1335]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1720,plain,
% 4.10/0.99      ( sK1 = k2_relat_1(sK3)
% 4.10/0.99      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 4.10/0.99      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1719]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1423,plain,
% 4.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 4.10/0.99      | r1_tarski(k2_relat_1(X0),sK1) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_376]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1634,plain,
% 4.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 4.10/0.99      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 4.10/0.99      inference(instantiation,[status(thm)],[c_1423]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1635,plain,
% 4.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 4.10/0.99      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 4.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1634]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_1526,plain,
% 4.10/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 4.10/0.99      inference(superposition,[status(thm)],[c_1177,c_1183]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(c_26,negated_conjecture,
% 4.10/0.99      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 4.10/0.99      inference(cnf_transformation,[],[f84]) ).
% 4.10/0.99  
% 4.10/0.99  cnf(contradiction,plain,
% 4.10/0.99      ( $false ),
% 4.10/0.99      inference(minisat,
% 4.10/0.99                [status(thm)],
% 4.10/0.99                [c_12217,c_1965,c_1720,c_1635,c_1526,c_26,c_38]) ).
% 4.10/0.99  
% 4.10/0.99  
% 4.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 4.10/0.99  
% 4.10/0.99  ------                               Statistics
% 4.10/0.99  
% 4.10/0.99  ------ General
% 4.10/0.99  
% 4.10/0.99  abstr_ref_over_cycles:                  0
% 4.10/0.99  abstr_ref_under_cycles:                 0
% 4.10/0.99  gc_basic_clause_elim:                   0
% 4.10/0.99  forced_gc_time:                         0
% 4.10/0.99  parsing_time:                           0.01
% 4.10/0.99  unif_index_cands_time:                  0.
% 4.10/0.99  unif_index_add_time:                    0.
% 4.10/0.99  orderings_time:                         0.
% 4.10/0.99  out_proof_time:                         0.014
% 4.10/0.99  total_time:                             0.424
% 4.10/0.99  num_of_symbols:                         55
% 4.10/0.99  num_of_terms:                           14714
% 4.10/0.99  
% 4.10/0.99  ------ Preprocessing
% 4.10/0.99  
% 4.10/0.99  num_of_splits:                          0
% 4.10/0.99  num_of_split_atoms:                     0
% 4.10/0.99  num_of_reused_defs:                     0
% 4.10/0.99  num_eq_ax_congr_red:                    10
% 4.10/0.99  num_of_sem_filtered_clauses:            1
% 4.10/0.99  num_of_subtypes:                        0
% 4.10/0.99  monotx_restored_types:                  0
% 4.10/0.99  sat_num_of_epr_types:                   0
% 4.10/0.99  sat_num_of_non_cyclic_types:            0
% 4.10/0.99  sat_guarded_non_collapsed_types:        0
% 4.10/0.99  num_pure_diseq_elim:                    0
% 4.10/0.99  simp_replaced_by:                       0
% 4.10/0.99  res_preprocessed:                       160
% 4.10/0.99  prep_upred:                             0
% 4.10/0.99  prep_unflattend:                        39
% 4.10/0.99  smt_new_axioms:                         0
% 4.10/0.99  pred_elim_cands:                        4
% 4.10/0.99  pred_elim:                              3
% 4.10/0.99  pred_elim_cl:                           5
% 4.10/0.99  pred_elim_cycles:                       5
% 4.10/0.99  merged_defs:                            0
% 4.10/0.99  merged_defs_ncl:                        0
% 4.10/0.99  bin_hyper_res:                          0
% 4.10/0.99  prep_cycles:                            4
% 4.10/0.99  pred_elim_time:                         0.005
% 4.10/0.99  splitting_time:                         0.
% 4.10/0.99  sem_filter_time:                        0.
% 4.10/0.99  monotx_time:                            0.001
% 4.10/0.99  subtype_inf_time:                       0.
% 4.10/0.99  
% 4.10/0.99  ------ Problem properties
% 4.10/0.99  
% 4.10/0.99  clauses:                                30
% 4.10/0.99  conjectures:                            7
% 4.10/0.99  epr:                                    5
% 4.10/0.99  horn:                                   27
% 4.10/0.99  ground:                                 15
% 4.10/0.99  unary:                                  9
% 4.10/0.99  binary:                                 8
% 4.10/0.99  lits:                                   72
% 4.10/0.99  lits_eq:                                24
% 4.10/0.99  fd_pure:                                0
% 4.10/0.99  fd_pseudo:                              0
% 4.10/0.99  fd_cond:                                0
% 4.10/0.99  fd_pseudo_cond:                         1
% 4.10/0.99  ac_symbols:                             0
% 4.10/0.99  
% 4.10/0.99  ------ Propositional Solver
% 4.10/0.99  
% 4.10/0.99  prop_solver_calls:                      32
% 4.10/0.99  prop_fast_solver_calls:                 1587
% 4.10/0.99  smt_solver_calls:                       0
% 4.10/0.99  smt_fast_solver_calls:                  0
% 4.10/0.99  prop_num_of_clauses:                    6444
% 4.10/0.99  prop_preprocess_simplified:             10224
% 4.10/0.99  prop_fo_subsumed:                       191
% 4.10/0.99  prop_solver_time:                       0.
% 4.10/0.99  smt_solver_time:                        0.
% 4.10/0.99  smt_fast_solver_time:                   0.
% 4.10/0.99  prop_fast_solver_time:                  0.
% 4.10/0.99  prop_unsat_core_time:                   0.
% 4.10/0.99  
% 4.10/0.99  ------ QBF
% 4.10/0.99  
% 4.10/0.99  qbf_q_res:                              0
% 4.10/0.99  qbf_num_tautologies:                    0
% 4.10/0.99  qbf_prep_cycles:                        0
% 4.10/0.99  
% 4.10/0.99  ------ BMC1
% 4.10/0.99  
% 4.10/0.99  bmc1_current_bound:                     -1
% 4.10/0.99  bmc1_last_solved_bound:                 -1
% 4.10/0.99  bmc1_unsat_core_size:                   -1
% 4.10/0.99  bmc1_unsat_core_parents_size:           -1
% 4.10/0.99  bmc1_merge_next_fun:                    0
% 4.10/0.99  bmc1_unsat_core_clauses_time:           0.
% 4.10/0.99  
% 4.10/0.99  ------ Instantiation
% 4.10/0.99  
% 4.10/0.99  inst_num_of_clauses:                    1683
% 4.10/0.99  inst_num_in_passive:                    201
% 4.10/0.99  inst_num_in_active:                     1029
% 4.10/0.99  inst_num_in_unprocessed:                453
% 4.10/0.99  inst_num_of_loops:                      1120
% 4.10/0.99  inst_num_of_learning_restarts:          0
% 4.10/0.99  inst_num_moves_active_passive:          85
% 4.10/0.99  inst_lit_activity:                      0
% 4.10/0.99  inst_lit_activity_moves:                0
% 4.10/0.99  inst_num_tautologies:                   0
% 4.10/0.99  inst_num_prop_implied:                  0
% 4.10/0.99  inst_num_existing_simplified:           0
% 4.10/0.99  inst_num_eq_res_simplified:             0
% 4.10/0.99  inst_num_child_elim:                    0
% 4.10/0.99  inst_num_of_dismatching_blockings:      609
% 4.10/0.99  inst_num_of_non_proper_insts:           2222
% 4.10/0.99  inst_num_of_duplicates:                 0
% 4.10/0.99  inst_inst_num_from_inst_to_res:         0
% 4.10/0.99  inst_dismatching_checking_time:         0.
% 4.10/0.99  
% 4.10/0.99  ------ Resolution
% 4.10/0.99  
% 4.10/0.99  res_num_of_clauses:                     0
% 4.10/0.99  res_num_in_passive:                     0
% 4.10/0.99  res_num_in_active:                      0
% 4.10/0.99  res_num_of_loops:                       164
% 4.10/0.99  res_forward_subset_subsumed:            168
% 4.10/0.99  res_backward_subset_subsumed:           0
% 4.10/0.99  res_forward_subsumed:                   0
% 4.10/0.99  res_backward_subsumed:                  0
% 4.10/0.99  res_forward_subsumption_resolution:     0
% 4.10/0.99  res_backward_subsumption_resolution:    0
% 4.10/0.99  res_clause_to_clause_subsumption:       1344
% 4.10/0.99  res_orphan_elimination:                 0
% 4.10/0.99  res_tautology_del:                      219
% 4.10/0.99  res_num_eq_res_simplified:              0
% 4.10/0.99  res_num_sel_changes:                    0
% 4.10/0.99  res_moves_from_active_to_pass:          0
% 4.10/0.99  
% 4.10/0.99  ------ Superposition
% 4.10/0.99  
% 4.10/0.99  sup_time_total:                         0.
% 4.10/0.99  sup_time_generating:                    0.
% 4.10/0.99  sup_time_sim_full:                      0.
% 4.10/0.99  sup_time_sim_immed:                     0.
% 4.10/0.99  
% 4.10/0.99  sup_num_of_clauses:                     545
% 4.10/0.99  sup_num_in_active:                      212
% 4.10/0.99  sup_num_in_passive:                     333
% 4.10/0.99  sup_num_of_loops:                       223
% 4.10/0.99  sup_fw_superposition:                   372
% 4.10/0.99  sup_bw_superposition:                   219
% 4.10/0.99  sup_immediate_simplified:               208
% 4.10/0.99  sup_given_eliminated:                   1
% 4.10/0.99  comparisons_done:                       0
% 4.10/0.99  comparisons_avoided:                    3
% 4.10/0.99  
% 4.10/0.99  ------ Simplifications
% 4.10/0.99  
% 4.10/0.99  
% 4.10/0.99  sim_fw_subset_subsumed:                 8
% 4.10/0.99  sim_bw_subset_subsumed:                 32
% 4.10/0.99  sim_fw_subsumed:                        10
% 4.10/0.99  sim_bw_subsumed:                        0
% 4.10/0.99  sim_fw_subsumption_res:                 0
% 4.10/0.99  sim_bw_subsumption_res:                 0
% 4.10/0.99  sim_tautology_del:                      0
% 4.10/0.99  sim_eq_tautology_del:                   24
% 4.10/0.99  sim_eq_res_simp:                        0
% 4.10/0.99  sim_fw_demodulated:                     12
% 4.10/0.99  sim_bw_demodulated:                     6
% 4.10/0.99  sim_light_normalised:                   193
% 4.10/0.99  sim_joinable_taut:                      0
% 4.10/0.99  sim_joinable_simp:                      0
% 4.10/0.99  sim_ac_normalised:                      0
% 4.10/0.99  sim_smt_subsumption:                    0
% 4.10/0.99  
%------------------------------------------------------------------------------
