%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:47 EST 2020

% Result     : Theorem 15.20s
% Output     : CNFRefutation 15.20s
% Verified   : 
% Statistics : Number of formulae       :  212 ( 635 expanded)
%              Number of clauses        :  132 ( 206 expanded)
%              Number of leaves         :   26 ( 161 expanded)
%              Depth                    :   16
%              Number of atoms          :  643 (3800 expanded)
%              Number of equality atoms :  284 ( 719 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( k2_relset_1(X0,X0,X1) = X0
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( k2_relset_1(X0,X0,X1) = X0
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f50,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & k2_relset_1(X0,X0,X1) = X0
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK3,k6_partfun1(X0))
        & k2_relset_1(X0,X0,X1) = X0
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK3,X0,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & k2_relset_1(X0,X0,X1) = X0
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1))
          & k2_relset_1(sK1,sK1,sK2) = sK1
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),sK2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
          & v1_funct_2(X2,sK1,sK1)
          & v1_funct_1(X2) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
      & v1_funct_2(sK2,sK1,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
    & k2_relset_1(sK1,sK1,sK2) = sK1
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK3,sK1,sK1)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    & v1_funct_2(sK2,sK1,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f51,f58,f57])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f90,plain,(
    k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f59])).

fof(f84,plain,(
    v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f46])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k7_relset_1(X0,X1,X3,X2),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k1_relat_1(X1) = k2_relat_1(X0) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f74])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f95,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f77,f80])).

fof(f91,plain,(
    ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_576,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_64652,plain,
    ( k1_relat_1(sK3) != X0
    | sK1 != X0
    | sK1 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_64653,plain,
    ( k1_relat_1(sK3) != sK1
    | sK1 = k1_relat_1(sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_64652])).

cnf(c_57243,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_59017,plain,
    ( X0 != k6_partfun1(k1_relat_1(sK3))
    | sK3 = X0
    | sK3 != k6_partfun1(k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_57243])).

cnf(c_59651,plain,
    ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(sK3))
    | sK3 != k6_partfun1(k1_relat_1(sK3))
    | sK3 = k6_partfun1(sK1) ),
    inference(instantiation,[status(thm)],[c_59017])).

cnf(c_583,plain,
    ( X0 != X1
    | k6_partfun1(X0) = k6_partfun1(X1) ),
    theory(equality)).

cnf(c_59591,plain,
    ( X0 != k1_relat_1(sK3)
    | k6_partfun1(X0) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_59596,plain,
    ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
    | sK1 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_59591])).

cnf(c_57541,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_57243])).

cnf(c_57980,plain,
    ( k6_partfun1(k1_relat_1(sK3)) != sK3
    | sK3 = k6_partfun1(k1_relat_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_57541])).

cnf(c_57309,plain,
    ( k2_relat_1(sK2) != X0
    | k2_relat_1(sK2) = k1_relat_1(sK3)
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_576])).

cnf(c_57310,plain,
    ( k2_relat_1(sK2) = k1_relat_1(sK3)
    | k2_relat_1(sK2) != sK1
    | k1_relat_1(sK3) != sK1 ),
    inference(instantiation,[status(thm)],[c_57309])).

cnf(c_591,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | r2_relset_1(X4,X5,X6,X7)
    | X4 != X0
    | X5 != X1
    | X6 != X2
    | X7 != X3 ),
    theory(equality)).

cnf(c_17777,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X5))
    | X0 != X4
    | X1 != X4
    | X2 != k6_partfun1(X4)
    | X3 != k6_partfun1(X5) ),
    inference(instantiation,[status(thm)],[c_591])).

cnf(c_52991,plain,
    ( ~ r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X1))
    | r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
    | k6_partfun1(sK1) != k6_partfun1(X1)
    | sK3 != k6_partfun1(X0)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_17777])).

cnf(c_52993,plain,
    ( ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK3 != k6_partfun1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_52991])).

cnf(c_580,plain,
    ( X0 != X1
    | k9_relat_1(X2,X0) = k9_relat_1(X2,X1) ),
    theory(equality)).

cnf(c_17128,plain,
    ( k9_relat_1(sK3,k2_relat_1(sK2)) = k9_relat_1(sK3,X0)
    | k2_relat_1(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_580])).

cnf(c_17133,plain,
    ( k9_relat_1(sK3,k2_relat_1(sK2)) = k9_relat_1(sK3,sK1)
    | k2_relat_1(sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_17128])).

cnf(c_577,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_10913,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X2)
    | X2 != X1
    | k9_relat_1(sK3,k2_relat_1(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_17127,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,X0),X1)
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X2)
    | X2 != X1
    | k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_10913])).

cnf(c_17129,plain,
    ( X0 != X1
    | k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,X2)
    | r1_tarski(k9_relat_1(sK3,X2),X1) != iProver_top
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17127])).

cnf(c_17131,plain,
    ( k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,sK1)
    | sK1 != sK1
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),sK1) = iProver_top
    | r1_tarski(k9_relat_1(sK3,sK1),sK1) != iProver_top ),
    inference(instantiation,[status(thm)],[c_17129])).

cnf(c_5456,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X2)
    | X2 != X1
    | k2_relat_1(k5_relat_1(sK2,sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_577])).

cnf(c_9836,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X0)
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X1)
    | X1 != X0
    | k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5456])).

cnf(c_9837,plain,
    ( X0 != X1
    | k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2))
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X1) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9836])).

cnf(c_9839,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2))
    | sK1 != sK1
    | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),sK1) != iProver_top
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_9837])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1073,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1075,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1078,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4955,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1078])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_34,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5522,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4955,c_34])).

cnf(c_5523,plain,
    ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5522])).

cnf(c_5534,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_5523])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1427,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1625,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_5673,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5534,c_30,c_28,c_27,c_25,c_1627])).

cnf(c_24,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1076,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5676,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK2,sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5673,c_1076])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1081,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1083,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4611,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | r1_tarski(k2_relat_1(X1),X3) != iProver_top
    | r1_tarski(k1_relat_1(X1),X2) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1083])).

cnf(c_7993,plain,
    ( sK2 = X0
    | r2_relset_1(sK1,sK1,X0,sK2) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
    | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_4611])).

cnf(c_8612,plain,
    ( k5_relat_1(sK2,sK3) = sK2
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
    | r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
    | v1_relat_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5676,c_7993])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1088,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1661,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1088])).

cnf(c_1662,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1073,c_1088])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1090,plain,
    ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3170,plain,
    ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1090])).

cnf(c_6315,plain,
    ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_1661,c_3170])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1087,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2281,plain,
    ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1075,c_1087])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_363,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK3 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_364,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(unflattening,[status(thm)],[c_363])).

cnf(c_366,plain,
    ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_27,c_25])).

cnf(c_2287,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2281,c_366])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1091,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1820,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1662,c_1091])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1086,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2045,plain,
    ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1073,c_1086])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2047,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2045,c_23])).

cnf(c_2282,plain,
    ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1073,c_1087])).

cnf(c_29,negated_conjecture,
    ( v1_funct_2(sK2,sK1,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1
    | sK2 != X0
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_372,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_374,plain,
    ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_372,c_30,c_28])).

cnf(c_2284,plain,
    ( k1_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2282,c_374])).

cnf(c_3546,plain,
    ( k10_relat_1(sK2,sK1) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1820,c_2047,c_2284])).

cnf(c_6321,plain,
    ( k1_relat_1(k5_relat_1(sK2,sK3)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_6315,c_2287,c_3546])).

cnf(c_8617,plain,
    ( k5_relat_1(sK2,sK3) = sK2
    | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_relat_1(k5_relat_1(sK2,sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8612,c_6321])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1085,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3099,plain,
    ( k7_relset_1(sK1,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1075,c_1085])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
    | ~ v1_funct_1(X0)
    | sK3 != X0
    | sK1 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_26])).

cnf(c_334,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1)
    | ~ v1_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_333])).

cnf(c_338,plain,
    ( r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_27,c_25])).

cnf(c_1071,plain,
    ( r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_3197,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),sK1) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3099,c_1071])).

cnf(c_3199,plain,
    ( r1_tarski(k9_relat_1(sK3,sK1),sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3197])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) = k9_relat_1(X0,k2_relat_1(X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1450,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k5_relat_1(X0,sK3)) = k9_relat_1(sK3,k2_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1747,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k5_relat_1(sK2,sK3)) = k9_relat_1(sK3,k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v1_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1448,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k5_relat_1(X0,sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1647,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_1648,plain,
    ( v1_relat_1(k5_relat_1(sK2,sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1647])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != X1
    | k6_partfun1(k1_relat_1(X0)) = X0
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1383,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(X0,sK3) != X0
    | k6_partfun1(k1_relat_1(sK3)) = sK3
    | k2_relat_1(X0) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1585,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK3)
    | k5_relat_1(sK2,sK3) != sK2
    | k6_partfun1(k1_relat_1(sK3)) = sK3
    | k2_relat_1(sK2) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1383])).

cnf(c_575,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1567,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_575])).

cnf(c_13,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1342,plain,
    ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1344,plain,
    ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
    | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_1301,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1301])).

cnf(c_1298,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1299,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1298])).

cnf(c_600,plain,
    ( k6_partfun1(sK1) = k6_partfun1(sK1)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_583])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_99,plain,
    ( ~ r1_tarski(sK1,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_94,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_96,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_95,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_52,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_22,negated_conjecture,
    ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_36,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_64653,c_59651,c_59596,c_57980,c_57310,c_52993,c_17133,c_17131,c_9839,c_8617,c_3199,c_2287,c_2047,c_1747,c_1648,c_1585,c_1567,c_1344,c_1302,c_1301,c_1299,c_1298,c_600,c_99,c_96,c_95,c_52,c_22,c_36,c_25,c_27,c_33,c_28,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:07:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.20/2.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.20/2.49  
% 15.20/2.49  ------  iProver source info
% 15.20/2.49  
% 15.20/2.49  git: date: 2020-06-30 10:37:57 +0100
% 15.20/2.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.20/2.49  git: non_committed_changes: false
% 15.20/2.49  git: last_make_outside_of_git: false
% 15.20/2.49  
% 15.20/2.49  ------ 
% 15.20/2.49  
% 15.20/2.49  ------ Input Options
% 15.20/2.49  
% 15.20/2.49  --out_options                           all
% 15.20/2.49  --tptp_safe_out                         true
% 15.20/2.49  --problem_path                          ""
% 15.20/2.49  --include_path                          ""
% 15.20/2.49  --clausifier                            res/vclausify_rel
% 15.20/2.49  --clausifier_options                    --mode clausify
% 15.20/2.49  --stdin                                 false
% 15.20/2.49  --stats_out                             all
% 15.20/2.49  
% 15.20/2.49  ------ General Options
% 15.20/2.49  
% 15.20/2.49  --fof                                   false
% 15.20/2.49  --time_out_real                         305.
% 15.20/2.49  --time_out_virtual                      -1.
% 15.20/2.49  --symbol_type_check                     false
% 15.20/2.49  --clausify_out                          false
% 15.20/2.49  --sig_cnt_out                           false
% 15.20/2.49  --trig_cnt_out                          false
% 15.20/2.49  --trig_cnt_out_tolerance                1.
% 15.20/2.49  --trig_cnt_out_sk_spl                   false
% 15.20/2.49  --abstr_cl_out                          false
% 15.20/2.49  
% 15.20/2.49  ------ Global Options
% 15.20/2.49  
% 15.20/2.49  --schedule                              default
% 15.20/2.49  --add_important_lit                     false
% 15.20/2.49  --prop_solver_per_cl                    1000
% 15.20/2.49  --min_unsat_core                        false
% 15.20/2.49  --soft_assumptions                      false
% 15.20/2.49  --soft_lemma_size                       3
% 15.20/2.49  --prop_impl_unit_size                   0
% 15.20/2.49  --prop_impl_unit                        []
% 15.20/2.49  --share_sel_clauses                     true
% 15.20/2.49  --reset_solvers                         false
% 15.20/2.49  --bc_imp_inh                            [conj_cone]
% 15.20/2.49  --conj_cone_tolerance                   3.
% 15.20/2.49  --extra_neg_conj                        none
% 15.20/2.49  --large_theory_mode                     true
% 15.20/2.49  --prolific_symb_bound                   200
% 15.20/2.49  --lt_threshold                          2000
% 15.20/2.49  --clause_weak_htbl                      true
% 15.20/2.49  --gc_record_bc_elim                     false
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing Options
% 15.20/2.49  
% 15.20/2.49  --preprocessing_flag                    true
% 15.20/2.49  --time_out_prep_mult                    0.1
% 15.20/2.49  --splitting_mode                        input
% 15.20/2.49  --splitting_grd                         true
% 15.20/2.49  --splitting_cvd                         false
% 15.20/2.49  --splitting_cvd_svl                     false
% 15.20/2.49  --splitting_nvd                         32
% 15.20/2.49  --sub_typing                            true
% 15.20/2.49  --prep_gs_sim                           true
% 15.20/2.49  --prep_unflatten                        true
% 15.20/2.49  --prep_res_sim                          true
% 15.20/2.49  --prep_upred                            true
% 15.20/2.49  --prep_sem_filter                       exhaustive
% 15.20/2.49  --prep_sem_filter_out                   false
% 15.20/2.49  --pred_elim                             true
% 15.20/2.49  --res_sim_input                         true
% 15.20/2.49  --eq_ax_congr_red                       true
% 15.20/2.49  --pure_diseq_elim                       true
% 15.20/2.49  --brand_transform                       false
% 15.20/2.49  --non_eq_to_eq                          false
% 15.20/2.49  --prep_def_merge                        true
% 15.20/2.49  --prep_def_merge_prop_impl              false
% 15.20/2.49  --prep_def_merge_mbd                    true
% 15.20/2.49  --prep_def_merge_tr_red                 false
% 15.20/2.49  --prep_def_merge_tr_cl                  false
% 15.20/2.49  --smt_preprocessing                     true
% 15.20/2.49  --smt_ac_axioms                         fast
% 15.20/2.49  --preprocessed_out                      false
% 15.20/2.49  --preprocessed_stats                    false
% 15.20/2.49  
% 15.20/2.49  ------ Abstraction refinement Options
% 15.20/2.49  
% 15.20/2.49  --abstr_ref                             []
% 15.20/2.49  --abstr_ref_prep                        false
% 15.20/2.49  --abstr_ref_until_sat                   false
% 15.20/2.49  --abstr_ref_sig_restrict                funpre
% 15.20/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.49  --abstr_ref_under                       []
% 15.20/2.49  
% 15.20/2.49  ------ SAT Options
% 15.20/2.49  
% 15.20/2.49  --sat_mode                              false
% 15.20/2.49  --sat_fm_restart_options                ""
% 15.20/2.49  --sat_gr_def                            false
% 15.20/2.49  --sat_epr_types                         true
% 15.20/2.49  --sat_non_cyclic_types                  false
% 15.20/2.49  --sat_finite_models                     false
% 15.20/2.49  --sat_fm_lemmas                         false
% 15.20/2.49  --sat_fm_prep                           false
% 15.20/2.49  --sat_fm_uc_incr                        true
% 15.20/2.49  --sat_out_model                         small
% 15.20/2.49  --sat_out_clauses                       false
% 15.20/2.49  
% 15.20/2.49  ------ QBF Options
% 15.20/2.49  
% 15.20/2.49  --qbf_mode                              false
% 15.20/2.49  --qbf_elim_univ                         false
% 15.20/2.49  --qbf_dom_inst                          none
% 15.20/2.49  --qbf_dom_pre_inst                      false
% 15.20/2.49  --qbf_sk_in                             false
% 15.20/2.49  --qbf_pred_elim                         true
% 15.20/2.49  --qbf_split                             512
% 15.20/2.49  
% 15.20/2.49  ------ BMC1 Options
% 15.20/2.49  
% 15.20/2.49  --bmc1_incremental                      false
% 15.20/2.49  --bmc1_axioms                           reachable_all
% 15.20/2.49  --bmc1_min_bound                        0
% 15.20/2.49  --bmc1_max_bound                        -1
% 15.20/2.49  --bmc1_max_bound_default                -1
% 15.20/2.49  --bmc1_symbol_reachability              true
% 15.20/2.49  --bmc1_property_lemmas                  false
% 15.20/2.49  --bmc1_k_induction                      false
% 15.20/2.49  --bmc1_non_equiv_states                 false
% 15.20/2.49  --bmc1_deadlock                         false
% 15.20/2.49  --bmc1_ucm                              false
% 15.20/2.49  --bmc1_add_unsat_core                   none
% 15.20/2.49  --bmc1_unsat_core_children              false
% 15.20/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.49  --bmc1_out_stat                         full
% 15.20/2.49  --bmc1_ground_init                      false
% 15.20/2.49  --bmc1_pre_inst_next_state              false
% 15.20/2.49  --bmc1_pre_inst_state                   false
% 15.20/2.49  --bmc1_pre_inst_reach_state             false
% 15.20/2.49  --bmc1_out_unsat_core                   false
% 15.20/2.49  --bmc1_aig_witness_out                  false
% 15.20/2.49  --bmc1_verbose                          false
% 15.20/2.49  --bmc1_dump_clauses_tptp                false
% 15.20/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.49  --bmc1_dump_file                        -
% 15.20/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.49  --bmc1_ucm_extend_mode                  1
% 15.20/2.49  --bmc1_ucm_init_mode                    2
% 15.20/2.49  --bmc1_ucm_cone_mode                    none
% 15.20/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.49  --bmc1_ucm_relax_model                  4
% 15.20/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.49  --bmc1_ucm_layered_model                none
% 15.20/2.49  --bmc1_ucm_max_lemma_size               10
% 15.20/2.49  
% 15.20/2.49  ------ AIG Options
% 15.20/2.49  
% 15.20/2.49  --aig_mode                              false
% 15.20/2.49  
% 15.20/2.49  ------ Instantiation Options
% 15.20/2.49  
% 15.20/2.49  --instantiation_flag                    true
% 15.20/2.49  --inst_sos_flag                         false
% 15.20/2.49  --inst_sos_phase                        true
% 15.20/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.49  --inst_lit_sel_side                     num_symb
% 15.20/2.49  --inst_solver_per_active                1400
% 15.20/2.49  --inst_solver_calls_frac                1.
% 15.20/2.49  --inst_passive_queue_type               priority_queues
% 15.20/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.49  --inst_passive_queues_freq              [25;2]
% 15.20/2.49  --inst_dismatching                      true
% 15.20/2.49  --inst_eager_unprocessed_to_passive     true
% 15.20/2.49  --inst_prop_sim_given                   true
% 15.20/2.49  --inst_prop_sim_new                     false
% 15.20/2.49  --inst_subs_new                         false
% 15.20/2.49  --inst_eq_res_simp                      false
% 15.20/2.49  --inst_subs_given                       false
% 15.20/2.49  --inst_orphan_elimination               true
% 15.20/2.49  --inst_learning_loop_flag               true
% 15.20/2.49  --inst_learning_start                   3000
% 15.20/2.49  --inst_learning_factor                  2
% 15.20/2.49  --inst_start_prop_sim_after_learn       3
% 15.20/2.49  --inst_sel_renew                        solver
% 15.20/2.49  --inst_lit_activity_flag                true
% 15.20/2.49  --inst_restr_to_given                   false
% 15.20/2.49  --inst_activity_threshold               500
% 15.20/2.49  --inst_out_proof                        true
% 15.20/2.49  
% 15.20/2.49  ------ Resolution Options
% 15.20/2.49  
% 15.20/2.49  --resolution_flag                       true
% 15.20/2.49  --res_lit_sel                           adaptive
% 15.20/2.49  --res_lit_sel_side                      none
% 15.20/2.49  --res_ordering                          kbo
% 15.20/2.49  --res_to_prop_solver                    active
% 15.20/2.49  --res_prop_simpl_new                    false
% 15.20/2.49  --res_prop_simpl_given                  true
% 15.20/2.49  --res_passive_queue_type                priority_queues
% 15.20/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.49  --res_passive_queues_freq               [15;5]
% 15.20/2.49  --res_forward_subs                      full
% 15.20/2.49  --res_backward_subs                     full
% 15.20/2.49  --res_forward_subs_resolution           true
% 15.20/2.49  --res_backward_subs_resolution          true
% 15.20/2.49  --res_orphan_elimination                true
% 15.20/2.49  --res_time_limit                        2.
% 15.20/2.49  --res_out_proof                         true
% 15.20/2.49  
% 15.20/2.49  ------ Superposition Options
% 15.20/2.49  
% 15.20/2.49  --superposition_flag                    true
% 15.20/2.49  --sup_passive_queue_type                priority_queues
% 15.20/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.49  --demod_completeness_check              fast
% 15.20/2.49  --demod_use_ground                      true
% 15.20/2.49  --sup_to_prop_solver                    passive
% 15.20/2.49  --sup_prop_simpl_new                    true
% 15.20/2.49  --sup_prop_simpl_given                  true
% 15.20/2.49  --sup_fun_splitting                     false
% 15.20/2.49  --sup_smt_interval                      50000
% 15.20/2.49  
% 15.20/2.49  ------ Superposition Simplification Setup
% 15.20/2.49  
% 15.20/2.49  --sup_indices_passive                   []
% 15.20/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_full_bw                           [BwDemod]
% 15.20/2.49  --sup_immed_triv                        [TrivRules]
% 15.20/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_immed_bw_main                     []
% 15.20/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.49  
% 15.20/2.49  ------ Combination Options
% 15.20/2.49  
% 15.20/2.49  --comb_res_mult                         3
% 15.20/2.49  --comb_sup_mult                         2
% 15.20/2.49  --comb_inst_mult                        10
% 15.20/2.49  
% 15.20/2.49  ------ Debug Options
% 15.20/2.49  
% 15.20/2.49  --dbg_backtrace                         false
% 15.20/2.49  --dbg_dump_prop_clauses                 false
% 15.20/2.49  --dbg_dump_prop_clauses_file            -
% 15.20/2.49  --dbg_out_stat                          false
% 15.20/2.49  ------ Parsing...
% 15.20/2.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.20/2.49  ------ Proving...
% 15.20/2.49  ------ Problem Properties 
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  clauses                                 30
% 15.20/2.49  conjectures                             7
% 15.20/2.49  EPR                                     4
% 15.20/2.49  Horn                                    30
% 15.20/2.49  unary                                   13
% 15.20/2.49  binary                                  7
% 15.20/2.49  lits                                    67
% 15.20/2.49  lits eq                                 17
% 15.20/2.49  fd_pure                                 0
% 15.20/2.49  fd_pseudo                               0
% 15.20/2.49  fd_cond                                 0
% 15.20/2.49  fd_pseudo_cond                          2
% 15.20/2.49  AC symbols                              0
% 15.20/2.49  
% 15.20/2.49  ------ Schedule dynamic 5 is on 
% 15.20/2.49  
% 15.20/2.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  ------ 
% 15.20/2.49  Current options:
% 15.20/2.49  ------ 
% 15.20/2.49  
% 15.20/2.49  ------ Input Options
% 15.20/2.49  
% 15.20/2.49  --out_options                           all
% 15.20/2.49  --tptp_safe_out                         true
% 15.20/2.49  --problem_path                          ""
% 15.20/2.49  --include_path                          ""
% 15.20/2.49  --clausifier                            res/vclausify_rel
% 15.20/2.49  --clausifier_options                    --mode clausify
% 15.20/2.49  --stdin                                 false
% 15.20/2.49  --stats_out                             all
% 15.20/2.49  
% 15.20/2.49  ------ General Options
% 15.20/2.49  
% 15.20/2.49  --fof                                   false
% 15.20/2.49  --time_out_real                         305.
% 15.20/2.49  --time_out_virtual                      -1.
% 15.20/2.49  --symbol_type_check                     false
% 15.20/2.49  --clausify_out                          false
% 15.20/2.49  --sig_cnt_out                           false
% 15.20/2.49  --trig_cnt_out                          false
% 15.20/2.49  --trig_cnt_out_tolerance                1.
% 15.20/2.49  --trig_cnt_out_sk_spl                   false
% 15.20/2.49  --abstr_cl_out                          false
% 15.20/2.49  
% 15.20/2.49  ------ Global Options
% 15.20/2.49  
% 15.20/2.49  --schedule                              default
% 15.20/2.49  --add_important_lit                     false
% 15.20/2.49  --prop_solver_per_cl                    1000
% 15.20/2.49  --min_unsat_core                        false
% 15.20/2.49  --soft_assumptions                      false
% 15.20/2.49  --soft_lemma_size                       3
% 15.20/2.49  --prop_impl_unit_size                   0
% 15.20/2.49  --prop_impl_unit                        []
% 15.20/2.49  --share_sel_clauses                     true
% 15.20/2.49  --reset_solvers                         false
% 15.20/2.49  --bc_imp_inh                            [conj_cone]
% 15.20/2.49  --conj_cone_tolerance                   3.
% 15.20/2.49  --extra_neg_conj                        none
% 15.20/2.49  --large_theory_mode                     true
% 15.20/2.49  --prolific_symb_bound                   200
% 15.20/2.49  --lt_threshold                          2000
% 15.20/2.49  --clause_weak_htbl                      true
% 15.20/2.49  --gc_record_bc_elim                     false
% 15.20/2.49  
% 15.20/2.49  ------ Preprocessing Options
% 15.20/2.49  
% 15.20/2.49  --preprocessing_flag                    true
% 15.20/2.49  --time_out_prep_mult                    0.1
% 15.20/2.49  --splitting_mode                        input
% 15.20/2.49  --splitting_grd                         true
% 15.20/2.49  --splitting_cvd                         false
% 15.20/2.49  --splitting_cvd_svl                     false
% 15.20/2.49  --splitting_nvd                         32
% 15.20/2.49  --sub_typing                            true
% 15.20/2.49  --prep_gs_sim                           true
% 15.20/2.49  --prep_unflatten                        true
% 15.20/2.49  --prep_res_sim                          true
% 15.20/2.49  --prep_upred                            true
% 15.20/2.49  --prep_sem_filter                       exhaustive
% 15.20/2.49  --prep_sem_filter_out                   false
% 15.20/2.49  --pred_elim                             true
% 15.20/2.49  --res_sim_input                         true
% 15.20/2.49  --eq_ax_congr_red                       true
% 15.20/2.49  --pure_diseq_elim                       true
% 15.20/2.49  --brand_transform                       false
% 15.20/2.49  --non_eq_to_eq                          false
% 15.20/2.49  --prep_def_merge                        true
% 15.20/2.49  --prep_def_merge_prop_impl              false
% 15.20/2.49  --prep_def_merge_mbd                    true
% 15.20/2.49  --prep_def_merge_tr_red                 false
% 15.20/2.49  --prep_def_merge_tr_cl                  false
% 15.20/2.49  --smt_preprocessing                     true
% 15.20/2.49  --smt_ac_axioms                         fast
% 15.20/2.49  --preprocessed_out                      false
% 15.20/2.49  --preprocessed_stats                    false
% 15.20/2.49  
% 15.20/2.49  ------ Abstraction refinement Options
% 15.20/2.49  
% 15.20/2.49  --abstr_ref                             []
% 15.20/2.49  --abstr_ref_prep                        false
% 15.20/2.49  --abstr_ref_until_sat                   false
% 15.20/2.49  --abstr_ref_sig_restrict                funpre
% 15.20/2.49  --abstr_ref_af_restrict_to_split_sk     false
% 15.20/2.49  --abstr_ref_under                       []
% 15.20/2.49  
% 15.20/2.49  ------ SAT Options
% 15.20/2.49  
% 15.20/2.49  --sat_mode                              false
% 15.20/2.49  --sat_fm_restart_options                ""
% 15.20/2.49  --sat_gr_def                            false
% 15.20/2.49  --sat_epr_types                         true
% 15.20/2.49  --sat_non_cyclic_types                  false
% 15.20/2.49  --sat_finite_models                     false
% 15.20/2.49  --sat_fm_lemmas                         false
% 15.20/2.49  --sat_fm_prep                           false
% 15.20/2.49  --sat_fm_uc_incr                        true
% 15.20/2.49  --sat_out_model                         small
% 15.20/2.49  --sat_out_clauses                       false
% 15.20/2.49  
% 15.20/2.49  ------ QBF Options
% 15.20/2.49  
% 15.20/2.49  --qbf_mode                              false
% 15.20/2.49  --qbf_elim_univ                         false
% 15.20/2.49  --qbf_dom_inst                          none
% 15.20/2.49  --qbf_dom_pre_inst                      false
% 15.20/2.49  --qbf_sk_in                             false
% 15.20/2.49  --qbf_pred_elim                         true
% 15.20/2.49  --qbf_split                             512
% 15.20/2.49  
% 15.20/2.49  ------ BMC1 Options
% 15.20/2.49  
% 15.20/2.49  --bmc1_incremental                      false
% 15.20/2.49  --bmc1_axioms                           reachable_all
% 15.20/2.49  --bmc1_min_bound                        0
% 15.20/2.49  --bmc1_max_bound                        -1
% 15.20/2.49  --bmc1_max_bound_default                -1
% 15.20/2.49  --bmc1_symbol_reachability              true
% 15.20/2.49  --bmc1_property_lemmas                  false
% 15.20/2.49  --bmc1_k_induction                      false
% 15.20/2.49  --bmc1_non_equiv_states                 false
% 15.20/2.49  --bmc1_deadlock                         false
% 15.20/2.49  --bmc1_ucm                              false
% 15.20/2.49  --bmc1_add_unsat_core                   none
% 15.20/2.49  --bmc1_unsat_core_children              false
% 15.20/2.49  --bmc1_unsat_core_extrapolate_axioms    false
% 15.20/2.49  --bmc1_out_stat                         full
% 15.20/2.49  --bmc1_ground_init                      false
% 15.20/2.49  --bmc1_pre_inst_next_state              false
% 15.20/2.49  --bmc1_pre_inst_state                   false
% 15.20/2.49  --bmc1_pre_inst_reach_state             false
% 15.20/2.49  --bmc1_out_unsat_core                   false
% 15.20/2.49  --bmc1_aig_witness_out                  false
% 15.20/2.49  --bmc1_verbose                          false
% 15.20/2.49  --bmc1_dump_clauses_tptp                false
% 15.20/2.49  --bmc1_dump_unsat_core_tptp             false
% 15.20/2.49  --bmc1_dump_file                        -
% 15.20/2.49  --bmc1_ucm_expand_uc_limit              128
% 15.20/2.49  --bmc1_ucm_n_expand_iterations          6
% 15.20/2.49  --bmc1_ucm_extend_mode                  1
% 15.20/2.49  --bmc1_ucm_init_mode                    2
% 15.20/2.49  --bmc1_ucm_cone_mode                    none
% 15.20/2.49  --bmc1_ucm_reduced_relation_type        0
% 15.20/2.49  --bmc1_ucm_relax_model                  4
% 15.20/2.49  --bmc1_ucm_full_tr_after_sat            true
% 15.20/2.49  --bmc1_ucm_expand_neg_assumptions       false
% 15.20/2.49  --bmc1_ucm_layered_model                none
% 15.20/2.49  --bmc1_ucm_max_lemma_size               10
% 15.20/2.49  
% 15.20/2.49  ------ AIG Options
% 15.20/2.49  
% 15.20/2.49  --aig_mode                              false
% 15.20/2.49  
% 15.20/2.49  ------ Instantiation Options
% 15.20/2.49  
% 15.20/2.49  --instantiation_flag                    true
% 15.20/2.49  --inst_sos_flag                         false
% 15.20/2.49  --inst_sos_phase                        true
% 15.20/2.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.20/2.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.20/2.49  --inst_lit_sel_side                     none
% 15.20/2.49  --inst_solver_per_active                1400
% 15.20/2.49  --inst_solver_calls_frac                1.
% 15.20/2.49  --inst_passive_queue_type               priority_queues
% 15.20/2.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.20/2.49  --inst_passive_queues_freq              [25;2]
% 15.20/2.49  --inst_dismatching                      true
% 15.20/2.49  --inst_eager_unprocessed_to_passive     true
% 15.20/2.49  --inst_prop_sim_given                   true
% 15.20/2.49  --inst_prop_sim_new                     false
% 15.20/2.49  --inst_subs_new                         false
% 15.20/2.49  --inst_eq_res_simp                      false
% 15.20/2.49  --inst_subs_given                       false
% 15.20/2.49  --inst_orphan_elimination               true
% 15.20/2.49  --inst_learning_loop_flag               true
% 15.20/2.49  --inst_learning_start                   3000
% 15.20/2.49  --inst_learning_factor                  2
% 15.20/2.49  --inst_start_prop_sim_after_learn       3
% 15.20/2.49  --inst_sel_renew                        solver
% 15.20/2.49  --inst_lit_activity_flag                true
% 15.20/2.49  --inst_restr_to_given                   false
% 15.20/2.49  --inst_activity_threshold               500
% 15.20/2.49  --inst_out_proof                        true
% 15.20/2.49  
% 15.20/2.49  ------ Resolution Options
% 15.20/2.49  
% 15.20/2.49  --resolution_flag                       false
% 15.20/2.49  --res_lit_sel                           adaptive
% 15.20/2.49  --res_lit_sel_side                      none
% 15.20/2.49  --res_ordering                          kbo
% 15.20/2.49  --res_to_prop_solver                    active
% 15.20/2.49  --res_prop_simpl_new                    false
% 15.20/2.49  --res_prop_simpl_given                  true
% 15.20/2.49  --res_passive_queue_type                priority_queues
% 15.20/2.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.20/2.49  --res_passive_queues_freq               [15;5]
% 15.20/2.49  --res_forward_subs                      full
% 15.20/2.49  --res_backward_subs                     full
% 15.20/2.49  --res_forward_subs_resolution           true
% 15.20/2.49  --res_backward_subs_resolution          true
% 15.20/2.49  --res_orphan_elimination                true
% 15.20/2.49  --res_time_limit                        2.
% 15.20/2.49  --res_out_proof                         true
% 15.20/2.49  
% 15.20/2.49  ------ Superposition Options
% 15.20/2.49  
% 15.20/2.49  --superposition_flag                    true
% 15.20/2.49  --sup_passive_queue_type                priority_queues
% 15.20/2.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.20/2.49  --sup_passive_queues_freq               [8;1;4]
% 15.20/2.49  --demod_completeness_check              fast
% 15.20/2.49  --demod_use_ground                      true
% 15.20/2.49  --sup_to_prop_solver                    passive
% 15.20/2.49  --sup_prop_simpl_new                    true
% 15.20/2.49  --sup_prop_simpl_given                  true
% 15.20/2.49  --sup_fun_splitting                     false
% 15.20/2.49  --sup_smt_interval                      50000
% 15.20/2.49  
% 15.20/2.49  ------ Superposition Simplification Setup
% 15.20/2.49  
% 15.20/2.49  --sup_indices_passive                   []
% 15.20/2.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 15.20/2.49  --sup_full_triv                         [TrivRules;PropSubs]
% 15.20/2.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_full_bw                           [BwDemod]
% 15.20/2.49  --sup_immed_triv                        [TrivRules]
% 15.20/2.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.20/2.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_immed_bw_main                     []
% 15.20/2.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.49  --sup_input_triv                        [Unflattening;TrivRules]
% 15.20/2.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 15.20/2.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 15.20/2.49  
% 15.20/2.49  ------ Combination Options
% 15.20/2.49  
% 15.20/2.49  --comb_res_mult                         3
% 15.20/2.49  --comb_sup_mult                         2
% 15.20/2.49  --comb_inst_mult                        10
% 15.20/2.49  
% 15.20/2.49  ------ Debug Options
% 15.20/2.49  
% 15.20/2.49  --dbg_backtrace                         false
% 15.20/2.49  --dbg_dump_prop_clauses                 false
% 15.20/2.49  --dbg_dump_prop_clauses_file            -
% 15.20/2.49  --dbg_out_stat                          false
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  ------ Proving...
% 15.20/2.49  
% 15.20/2.49  
% 15.20/2.49  % SZS status Theorem for theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  % SZS output start CNFRefutation for theBenchmark.p
% 15.20/2.49  
% 15.20/2.49  fof(f21,conjecture,(
% 15.20/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f22,negated_conjecture,(
% 15.20/2.49    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 15.20/2.49    inference(negated_conjecture,[],[f21])).
% 15.20/2.49  
% 15.20/2.49  fof(f50,plain,(
% 15.20/2.49    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 15.20/2.49    inference(ennf_transformation,[],[f22])).
% 15.20/2.49  
% 15.20/2.49  fof(f51,plain,(
% 15.20/2.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 15.20/2.49    inference(flattening,[],[f50])).
% 15.20/2.49  
% 15.20/2.49  fof(f58,plain,(
% 15.20/2.49    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK3,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,sK3),X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK3,X0,X0) & v1_funct_1(sK3))) )),
% 15.20/2.49    introduced(choice_axiom,[])).
% 15.20/2.49  
% 15.20/2.49  fof(f57,plain,(
% 15.20/2.49    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & k2_relset_1(X0,X0,X1) = X0 & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X1,X2),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK1,sK1,X2,k6_partfun1(sK1)) & k2_relset_1(sK1,sK1,sK2) = sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,X2),sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(X2,sK1,sK1) & v1_funct_1(X2)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2))),
% 15.20/2.49    introduced(choice_axiom,[])).
% 15.20/2.49  
% 15.20/2.49  fof(f59,plain,(
% 15.20/2.49    (~r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) & k2_relset_1(sK1,sK1,sK2) = sK1 & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK3,sK1,sK1) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) & v1_funct_2(sK2,sK1,sK1) & v1_funct_1(sK2)),
% 15.20/2.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f51,f58,f57])).
% 15.20/2.49  
% 15.20/2.49  fof(f85,plain,(
% 15.20/2.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f88,plain,(
% 15.20/2.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f17,axiom,(
% 15.20/2.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f44,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.20/2.49    inference(ennf_transformation,[],[f17])).
% 15.20/2.49  
% 15.20/2.49  fof(f45,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.20/2.49    inference(flattening,[],[f44])).
% 15.20/2.49  
% 15.20/2.49  fof(f79,plain,(
% 15.20/2.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f45])).
% 15.20/2.49  
% 15.20/2.49  fof(f86,plain,(
% 15.20/2.49    v1_funct_1(sK3)),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f83,plain,(
% 15.20/2.49    v1_funct_1(sK2)),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f89,plain,(
% 15.20/2.49    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2)),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f14,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f40,plain,(
% 15.20/2.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 15.20/2.49    inference(ennf_transformation,[],[f14])).
% 15.20/2.49  
% 15.20/2.49  fof(f41,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 15.20/2.49    inference(flattening,[],[f40])).
% 15.20/2.49  
% 15.20/2.49  fof(f76,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f41])).
% 15.20/2.49  
% 15.20/2.49  fof(f12,axiom,(
% 15.20/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f36,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.20/2.49    inference(ennf_transformation,[],[f12])).
% 15.20/2.49  
% 15.20/2.49  fof(f37,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(flattening,[],[f36])).
% 15.20/2.49  
% 15.20/2.49  fof(f54,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(nnf_transformation,[],[f37])).
% 15.20/2.49  
% 15.20/2.49  fof(f73,plain,(
% 15.20/2.49    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f54])).
% 15.20/2.49  
% 15.20/2.49  fof(f8,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f32,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(ennf_transformation,[],[f8])).
% 15.20/2.49  
% 15.20/2.49  fof(f69,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f32])).
% 15.20/2.49  
% 15.20/2.49  fof(f6,axiom,(
% 15.20/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1))))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f29,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f6])).
% 15.20/2.49  
% 15.20/2.49  fof(f67,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k1_relat_1(k5_relat_1(X0,X1)) = k10_relat_1(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f29])).
% 15.20/2.49  
% 15.20/2.49  fof(f9,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f33,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(ennf_transformation,[],[f9])).
% 15.20/2.49  
% 15.20/2.49  fof(f70,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f33])).
% 15.20/2.49  
% 15.20/2.49  fof(f20,axiom,(
% 15.20/2.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f48,plain,(
% 15.20/2.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 15.20/2.49    inference(ennf_transformation,[],[f20])).
% 15.20/2.49  
% 15.20/2.49  fof(f49,plain,(
% 15.20/2.49    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 15.20/2.49    inference(flattening,[],[f48])).
% 15.20/2.49  
% 15.20/2.49  fof(f82,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f49])).
% 15.20/2.49  
% 15.20/2.49  fof(f87,plain,(
% 15.20/2.49    v1_funct_2(sK3,sK1,sK1)),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f5,axiom,(
% 15.20/2.49    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f28,plain,(
% 15.20/2.49    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f5])).
% 15.20/2.49  
% 15.20/2.49  fof(f66,plain,(
% 15.20/2.49    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f28])).
% 15.20/2.49  
% 15.20/2.49  fof(f10,axiom,(
% 15.20/2.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f34,plain,(
% 15.20/2.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(ennf_transformation,[],[f10])).
% 15.20/2.49  
% 15.20/2.49  fof(f71,plain,(
% 15.20/2.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f34])).
% 15.20/2.49  
% 15.20/2.49  fof(f90,plain,(
% 15.20/2.49    k2_relset_1(sK1,sK1,sK2) = sK1),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f84,plain,(
% 15.20/2.49    v1_funct_2(sK2,sK1,sK1)),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  fof(f11,axiom,(
% 15.20/2.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f35,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.20/2.49    inference(ennf_transformation,[],[f11])).
% 15.20/2.49  
% 15.20/2.49  fof(f72,plain,(
% 15.20/2.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f35])).
% 15.20/2.49  
% 15.20/2.49  fof(f19,axiom,(
% 15.20/2.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => r1_tarski(k7_relset_1(X0,X1,X3,X2),X1))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f46,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 15.20/2.49    inference(ennf_transformation,[],[f19])).
% 15.20/2.49  
% 15.20/2.49  fof(f47,plain,(
% 15.20/2.49    ! [X0,X1,X2,X3] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 15.20/2.49    inference(flattening,[],[f46])).
% 15.20/2.49  
% 15.20/2.49  fof(f81,plain,(
% 15.20/2.49    ( ! [X2,X0,X3,X1] : (r1_tarski(k7_relset_1(X0,X1,X3,X2),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f47])).
% 15.20/2.49  
% 15.20/2.49  fof(f4,axiom,(
% 15.20/2.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1))))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f27,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.20/2.49    inference(ennf_transformation,[],[f4])).
% 15.20/2.49  
% 15.20/2.49  fof(f65,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f27])).
% 15.20/2.49  
% 15.20/2.49  fof(f2,axiom,(
% 15.20/2.49    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f24,plain,(
% 15.20/2.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f2])).
% 15.20/2.49  
% 15.20/2.49  fof(f25,plain,(
% 15.20/2.49    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 15.20/2.49    inference(flattening,[],[f24])).
% 15.20/2.49  
% 15.20/2.49  fof(f63,plain,(
% 15.20/2.49    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f25])).
% 15.20/2.49  
% 15.20/2.49  fof(f7,axiom,(
% 15.20/2.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k1_relat_1(X1) = k2_relat_1(X0)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f30,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.20/2.49    inference(ennf_transformation,[],[f7])).
% 15.20/2.49  
% 15.20/2.49  fof(f31,plain,(
% 15.20/2.49    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.20/2.49    inference(flattening,[],[f30])).
% 15.20/2.49  
% 15.20/2.49  fof(f68,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f31])).
% 15.20/2.49  
% 15.20/2.49  fof(f18,axiom,(
% 15.20/2.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f80,plain,(
% 15.20/2.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f18])).
% 15.20/2.49  
% 15.20/2.49  fof(f92,plain,(
% 15.20/2.49    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k1_relat_1(X1) != k2_relat_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.20/2.49    inference(definition_unfolding,[],[f68,f80])).
% 15.20/2.49  
% 15.20/2.49  fof(f74,plain,(
% 15.20/2.49    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f54])).
% 15.20/2.49  
% 15.20/2.49  fof(f96,plain,(
% 15.20/2.49    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.20/2.49    inference(equality_resolution,[],[f74])).
% 15.20/2.49  
% 15.20/2.49  fof(f1,axiom,(
% 15.20/2.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f52,plain,(
% 15.20/2.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.20/2.49    inference(nnf_transformation,[],[f1])).
% 15.20/2.49  
% 15.20/2.49  fof(f53,plain,(
% 15.20/2.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.20/2.49    inference(flattening,[],[f52])).
% 15.20/2.49  
% 15.20/2.49  fof(f62,plain,(
% 15.20/2.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.20/2.49    inference(cnf_transformation,[],[f53])).
% 15.20/2.49  
% 15.20/2.49  fof(f60,plain,(
% 15.20/2.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.20/2.49    inference(cnf_transformation,[],[f53])).
% 15.20/2.49  
% 15.20/2.49  fof(f95,plain,(
% 15.20/2.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.20/2.49    inference(equality_resolution,[],[f60])).
% 15.20/2.49  
% 15.20/2.49  fof(f15,axiom,(
% 15.20/2.49    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 15.20/2.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.20/2.49  
% 15.20/2.49  fof(f77,plain,(
% 15.20/2.49    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.20/2.49    inference(cnf_transformation,[],[f15])).
% 15.20/2.49  
% 15.20/2.49  fof(f93,plain,(
% 15.20/2.49    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 15.20/2.49    inference(definition_unfolding,[],[f77,f80])).
% 15.20/2.49  
% 15.20/2.49  fof(f91,plain,(
% 15.20/2.49    ~r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))),
% 15.20/2.49    inference(cnf_transformation,[],[f59])).
% 15.20/2.49  
% 15.20/2.49  cnf(c_576,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_64652,plain,
% 15.20/2.49      ( k1_relat_1(sK3) != X0 | sK1 != X0 | sK1 = k1_relat_1(sK3) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_576]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_64653,plain,
% 15.20/2.49      ( k1_relat_1(sK3) != sK1 | sK1 = k1_relat_1(sK3) | sK1 != sK1 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_64652]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_57243,plain,
% 15.20/2.49      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_576]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_59017,plain,
% 15.20/2.49      ( X0 != k6_partfun1(k1_relat_1(sK3))
% 15.20/2.49      | sK3 = X0
% 15.20/2.49      | sK3 != k6_partfun1(k1_relat_1(sK3)) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_57243]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_59651,plain,
% 15.20/2.49      ( k6_partfun1(sK1) != k6_partfun1(k1_relat_1(sK3))
% 15.20/2.49      | sK3 != k6_partfun1(k1_relat_1(sK3))
% 15.20/2.49      | sK3 = k6_partfun1(sK1) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_59017]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_583,plain,
% 15.20/2.49      ( X0 != X1 | k6_partfun1(X0) = k6_partfun1(X1) ),
% 15.20/2.49      theory(equality) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_59591,plain,
% 15.20/2.49      ( X0 != k1_relat_1(sK3)
% 15.20/2.49      | k6_partfun1(X0) = k6_partfun1(k1_relat_1(sK3)) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_583]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_59596,plain,
% 15.20/2.49      ( k6_partfun1(sK1) = k6_partfun1(k1_relat_1(sK3))
% 15.20/2.49      | sK1 != k1_relat_1(sK3) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_59591]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_57541,plain,
% 15.20/2.49      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_57243]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_57980,plain,
% 15.20/2.49      ( k6_partfun1(k1_relat_1(sK3)) != sK3
% 15.20/2.49      | sK3 = k6_partfun1(k1_relat_1(sK3))
% 15.20/2.49      | sK3 != sK3 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_57541]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_57309,plain,
% 15.20/2.49      ( k2_relat_1(sK2) != X0
% 15.20/2.49      | k2_relat_1(sK2) = k1_relat_1(sK3)
% 15.20/2.49      | k1_relat_1(sK3) != X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_576]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_57310,plain,
% 15.20/2.49      ( k2_relat_1(sK2) = k1_relat_1(sK3)
% 15.20/2.49      | k2_relat_1(sK2) != sK1
% 15.20/2.49      | k1_relat_1(sK3) != sK1 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_57309]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_591,plain,
% 15.20/2.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.20/2.49      | r2_relset_1(X4,X5,X6,X7)
% 15.20/2.49      | X4 != X0
% 15.20/2.49      | X5 != X1
% 15.20/2.49      | X6 != X2
% 15.20/2.49      | X7 != X3 ),
% 15.20/2.49      theory(equality) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17777,plain,
% 15.20/2.49      ( r2_relset_1(X0,X1,X2,X3)
% 15.20/2.49      | ~ r2_relset_1(X4,X4,k6_partfun1(X4),k6_partfun1(X5))
% 15.20/2.49      | X0 != X4
% 15.20/2.49      | X1 != X4
% 15.20/2.49      | X2 != k6_partfun1(X4)
% 15.20/2.49      | X3 != k6_partfun1(X5) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_591]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_52991,plain,
% 15.20/2.49      ( ~ r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X1))
% 15.20/2.49      | r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
% 15.20/2.49      | k6_partfun1(sK1) != k6_partfun1(X1)
% 15.20/2.49      | sK3 != k6_partfun1(X0)
% 15.20/2.49      | sK1 != X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_17777]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_52993,plain,
% 15.20/2.49      ( ~ r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 15.20/2.49      | r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1))
% 15.20/2.49      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 15.20/2.49      | sK3 != k6_partfun1(sK1)
% 15.20/2.49      | sK1 != sK1 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_52991]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_580,plain,
% 15.20/2.49      ( X0 != X1 | k9_relat_1(X2,X0) = k9_relat_1(X2,X1) ),
% 15.20/2.49      theory(equality) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17128,plain,
% 15.20/2.49      ( k9_relat_1(sK3,k2_relat_1(sK2)) = k9_relat_1(sK3,X0)
% 15.20/2.49      | k2_relat_1(sK2) != X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_580]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17133,plain,
% 15.20/2.49      ( k9_relat_1(sK3,k2_relat_1(sK2)) = k9_relat_1(sK3,sK1)
% 15.20/2.49      | k2_relat_1(sK2) != sK1 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_17128]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_577,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.20/2.49      theory(equality) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10913,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1)
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X2)
% 15.20/2.49      | X2 != X1
% 15.20/2.49      | k9_relat_1(sK3,k2_relat_1(sK2)) != X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_577]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17127,plain,
% 15.20/2.49      ( ~ r1_tarski(k9_relat_1(sK3,X0),X1)
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X2)
% 15.20/2.49      | X2 != X1
% 15.20/2.49      | k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,X0) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_10913]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17129,plain,
% 15.20/2.49      ( X0 != X1
% 15.20/2.49      | k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,X2)
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,X2),X1) != iProver_top
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_17127]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_17131,plain,
% 15.20/2.49      ( k9_relat_1(sK3,k2_relat_1(sK2)) != k9_relat_1(sK3,sK1)
% 15.20/2.49      | sK1 != sK1
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),sK1) = iProver_top
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,sK1),sK1) != iProver_top ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_17129]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5456,plain,
% 15.20/2.49      ( ~ r1_tarski(X0,X1)
% 15.20/2.49      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X2)
% 15.20/2.49      | X2 != X1
% 15.20/2.49      | k2_relat_1(k5_relat_1(sK2,sK3)) != X0 ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_577]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9836,plain,
% 15.20/2.49      ( ~ r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X0)
% 15.20/2.49      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X1)
% 15.20/2.49      | X1 != X0
% 15.20/2.49      | k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2)) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_5456]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9837,plain,
% 15.20/2.49      ( X0 != X1
% 15.20/2.49      | k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2))
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),X1) != iProver_top
% 15.20/2.49      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),X0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_9836]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9839,plain,
% 15.20/2.49      ( k2_relat_1(k5_relat_1(sK2,sK3)) != k9_relat_1(sK3,k2_relat_1(sK2))
% 15.20/2.49      | sK1 != sK1
% 15.20/2.49      | r1_tarski(k9_relat_1(sK3,k2_relat_1(sK2)),sK1) != iProver_top
% 15.20/2.49      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) = iProver_top ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_9837]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_28,negated_conjecture,
% 15.20/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 15.20/2.49      inference(cnf_transformation,[],[f85]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1073,plain,
% 15.20/2.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_25,negated_conjecture,
% 15.20/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 15.20/2.49      inference(cnf_transformation,[],[f88]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1075,plain,
% 15.20/2.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_19,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.20/2.49      | ~ v1_funct_1(X0)
% 15.20/2.49      | ~ v1_funct_1(X3)
% 15.20/2.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f79]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1078,plain,
% 15.20/2.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.20/2.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.20/2.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.20/2.49      | v1_funct_1(X5) != iProver_top
% 15.20/2.49      | v1_funct_1(X4) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_4955,plain,
% 15.20/2.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
% 15.20/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.20/2.49      | v1_funct_1(X2) != iProver_top
% 15.20/2.49      | v1_funct_1(sK3) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1075,c_1078]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_27,negated_conjecture,
% 15.20/2.49      ( v1_funct_1(sK3) ),
% 15.20/2.49      inference(cnf_transformation,[],[f86]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_34,plain,
% 15.20/2.49      ( v1_funct_1(sK3) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5522,plain,
% 15.20/2.49      ( v1_funct_1(X2) != iProver_top
% 15.20/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.20/2.49      | k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3) ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_4955,c_34]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5523,plain,
% 15.20/2.49      ( k1_partfun1(X0,X1,sK1,sK1,X2,sK3) = k5_relat_1(X2,sK3)
% 15.20/2.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.20/2.49      | v1_funct_1(X2) != iProver_top ),
% 15.20/2.49      inference(renaming,[status(thm)],[c_5522]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5534,plain,
% 15.20/2.49      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3)
% 15.20/2.49      | v1_funct_1(sK2) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1073,c_5523]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_30,negated_conjecture,
% 15.20/2.49      ( v1_funct_1(sK2) ),
% 15.20/2.49      inference(cnf_transformation,[],[f83]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1427,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 15.20/2.49      | ~ v1_funct_1(X0)
% 15.20/2.49      | ~ v1_funct_1(sK3)
% 15.20/2.49      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_19]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1625,plain,
% 15.20/2.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.20/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 15.20/2.49      | ~ v1_funct_1(sK2)
% 15.20/2.49      | ~ v1_funct_1(sK3)
% 15.20/2.49      | k1_partfun1(X0,X1,X2,X3,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_1427]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1627,plain,
% 15.20/2.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.49      | ~ v1_funct_1(sK2)
% 15.20/2.49      | ~ v1_funct_1(sK3)
% 15.20/2.49      | k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.20/2.49      inference(instantiation,[status(thm)],[c_1625]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5673,plain,
% 15.20/2.49      ( k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 15.20/2.49      inference(global_propositional_subsumption,
% 15.20/2.49                [status(thm)],
% 15.20/2.49                [c_5534,c_30,c_28,c_27,c_25,c_1627]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_24,negated_conjecture,
% 15.20/2.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) ),
% 15.20/2.49      inference(cnf_transformation,[],[f89]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1076,plain,
% 15.20/2.49      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK1,sK1,sK1,sK2,sK3),sK2) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_5676,plain,
% 15.20/2.49      ( r2_relset_1(sK1,sK1,k5_relat_1(sK2,sK3),sK2) = iProver_top ),
% 15.20/2.49      inference(demodulation,[status(thm)],[c_5673,c_1076]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_16,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.49      | ~ r1_tarski(k2_relat_1(X0),X2)
% 15.20/2.49      | ~ r1_tarski(k1_relat_1(X0),X1)
% 15.20/2.49      | ~ v1_relat_1(X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f76]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1081,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 15.20/2.49      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 15.20/2.49      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 15.20/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_14,plain,
% 15.20/2.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 15.20/2.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.20/2.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 15.20/2.49      | X3 = X2 ),
% 15.20/2.49      inference(cnf_transformation,[],[f73]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1083,plain,
% 15.20/2.49      ( X0 = X1
% 15.20/2.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 15.20/2.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_4611,plain,
% 15.20/2.49      ( X0 = X1
% 15.20/2.49      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 15.20/2.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.20/2.49      | r1_tarski(k2_relat_1(X1),X3) != iProver_top
% 15.20/2.49      | r1_tarski(k1_relat_1(X1),X2) != iProver_top
% 15.20/2.49      | v1_relat_1(X1) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1081,c_1083]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_7993,plain,
% 15.20/2.49      ( sK2 = X0
% 15.20/2.49      | r2_relset_1(sK1,sK1,X0,sK2) != iProver_top
% 15.20/2.49      | r1_tarski(k2_relat_1(X0),sK1) != iProver_top
% 15.20/2.49      | r1_tarski(k1_relat_1(X0),sK1) != iProver_top
% 15.20/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1073,c_4611]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_8612,plain,
% 15.20/2.49      ( k5_relat_1(sK2,sK3) = sK2
% 15.20/2.49      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
% 15.20/2.49      | r1_tarski(k1_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
% 15.20/2.49      | v1_relat_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_5676,c_7993]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_9,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.49      | v1_relat_1(X0) ),
% 15.20/2.49      inference(cnf_transformation,[],[f69]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1088,plain,
% 15.20/2.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.20/2.49      | v1_relat_1(X0) = iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1661,plain,
% 15.20/2.49      ( v1_relat_1(sK3) = iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1075,c_1088]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1662,plain,
% 15.20/2.49      ( v1_relat_1(sK2) = iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1073,c_1088]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_7,plain,
% 15.20/2.49      ( ~ v1_relat_1(X0)
% 15.20/2.49      | ~ v1_relat_1(X1)
% 15.20/2.49      | k10_relat_1(X1,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(X1,X0)) ),
% 15.20/2.49      inference(cnf_transformation,[],[f67]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_1090,plain,
% 15.20/2.49      ( k10_relat_1(X0,k1_relat_1(X1)) = k1_relat_1(k5_relat_1(X0,X1))
% 15.20/2.49      | v1_relat_1(X1) != iProver_top
% 15.20/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.20/2.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_3170,plain,
% 15.20/2.49      ( k10_relat_1(sK2,k1_relat_1(X0)) = k1_relat_1(k5_relat_1(sK2,X0))
% 15.20/2.49      | v1_relat_1(X0) != iProver_top ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1662,c_1090]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_6315,plain,
% 15.20/2.49      ( k10_relat_1(sK2,k1_relat_1(sK3)) = k1_relat_1(k5_relat_1(sK2,sK3)) ),
% 15.20/2.49      inference(superposition,[status(thm)],[c_1661,c_3170]) ).
% 15.20/2.49  
% 15.20/2.49  cnf(c_10,plain,
% 15.20/2.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1087,plain,
% 15.20/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.20/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2281,plain,
% 15.20/2.50      ( k1_relset_1(sK1,sK1,sK3) = k1_relat_1(sK3) ),
% 15.20/2.50      inference(superposition,[status(thm)],[c_1075,c_1087]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_21,plain,
% 15.20/2.50      ( ~ v1_funct_2(X0,X1,X1)
% 15.20/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 15.20/2.50      | ~ v1_funct_1(X0)
% 15.20/2.50      | k1_relset_1(X1,X1,X0) = X1 ),
% 15.20/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_26,negated_conjecture,
% 15.20/2.50      ( v1_funct_2(sK3,sK1,sK1) ),
% 15.20/2.50      inference(cnf_transformation,[],[f87]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_363,plain,
% 15.20/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 15.20/2.50      | ~ v1_funct_1(X0)
% 15.20/2.50      | k1_relset_1(X1,X1,X0) = X1
% 15.20/2.50      | sK3 != X0
% 15.20/2.50      | sK1 != X1 ),
% 15.20/2.50      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_364,plain,
% 15.20/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.50      | ~ v1_funct_1(sK3)
% 15.20/2.50      | k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 15.20/2.50      inference(unflattening,[status(thm)],[c_363]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_366,plain,
% 15.20/2.50      ( k1_relset_1(sK1,sK1,sK3) = sK1 ),
% 15.20/2.50      inference(global_propositional_subsumption,
% 15.20/2.50                [status(thm)],
% 15.20/2.50                [c_364,c_27,c_25]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2287,plain,
% 15.20/2.50      ( k1_relat_1(sK3) = sK1 ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_2281,c_366]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_6,plain,
% 15.20/2.50      ( ~ v1_relat_1(X0)
% 15.20/2.50      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f66]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1091,plain,
% 15.20/2.50      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 15.20/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1820,plain,
% 15.20/2.50      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 15.20/2.50      inference(superposition,[status(thm)],[c_1662,c_1091]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_11,plain,
% 15.20/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1086,plain,
% 15.20/2.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.20/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2045,plain,
% 15.20/2.50      ( k2_relset_1(sK1,sK1,sK2) = k2_relat_1(sK2) ),
% 15.20/2.50      inference(superposition,[status(thm)],[c_1073,c_1086]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_23,negated_conjecture,
% 15.20/2.50      ( k2_relset_1(sK1,sK1,sK2) = sK1 ),
% 15.20/2.50      inference(cnf_transformation,[],[f90]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2047,plain,
% 15.20/2.50      ( k2_relat_1(sK2) = sK1 ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_2045,c_23]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2282,plain,
% 15.20/2.50      ( k1_relset_1(sK1,sK1,sK2) = k1_relat_1(sK2) ),
% 15.20/2.50      inference(superposition,[status(thm)],[c_1073,c_1087]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_29,negated_conjecture,
% 15.20/2.50      ( v1_funct_2(sK2,sK1,sK1) ),
% 15.20/2.50      inference(cnf_transformation,[],[f84]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_371,plain,
% 15.20/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 15.20/2.50      | ~ v1_funct_1(X0)
% 15.20/2.50      | k1_relset_1(X1,X1,X0) = X1
% 15.20/2.50      | sK2 != X0
% 15.20/2.50      | sK1 != X1 ),
% 15.20/2.50      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_372,plain,
% 15.20/2.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.50      | ~ v1_funct_1(sK2)
% 15.20/2.50      | k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 15.20/2.50      inference(unflattening,[status(thm)],[c_371]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_374,plain,
% 15.20/2.50      ( k1_relset_1(sK1,sK1,sK2) = sK1 ),
% 15.20/2.50      inference(global_propositional_subsumption,
% 15.20/2.50                [status(thm)],
% 15.20/2.50                [c_372,c_30,c_28]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2284,plain,
% 15.20/2.50      ( k1_relat_1(sK2) = sK1 ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_2282,c_374]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_3546,plain,
% 15.20/2.50      ( k10_relat_1(sK2,sK1) = sK1 ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_1820,c_2047,c_2284]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_6321,plain,
% 15.20/2.50      ( k1_relat_1(k5_relat_1(sK2,sK3)) = sK1 ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_6315,c_2287,c_3546]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_8617,plain,
% 15.20/2.50      ( k5_relat_1(sK2,sK3) = sK2
% 15.20/2.50      | r1_tarski(k2_relat_1(k5_relat_1(sK2,sK3)),sK1) != iProver_top
% 15.20/2.50      | r1_tarski(sK1,sK1) != iProver_top
% 15.20/2.50      | v1_relat_1(k5_relat_1(sK2,sK3)) != iProver_top ),
% 15.20/2.50      inference(light_normalisation,[status(thm)],[c_8612,c_6321]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_12,plain,
% 15.20/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.50      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 15.20/2.50      inference(cnf_transformation,[],[f72]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1085,plain,
% 15.20/2.50      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 15.20/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_3099,plain,
% 15.20/2.50      ( k7_relset_1(sK1,sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 15.20/2.50      inference(superposition,[status(thm)],[c_1075,c_1085]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_20,plain,
% 15.20/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.20/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.50      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
% 15.20/2.50      | ~ v1_funct_1(X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_333,plain,
% 15.20/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.20/2.50      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2)
% 15.20/2.50      | ~ v1_funct_1(X0)
% 15.20/2.50      | sK3 != X0
% 15.20/2.50      | sK1 != X2
% 15.20/2.50      | sK1 != X1 ),
% 15.20/2.50      inference(resolution_lifted,[status(thm)],[c_20,c_26]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_334,plain,
% 15.20/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.50      | r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1)
% 15.20/2.50      | ~ v1_funct_1(sK3) ),
% 15.20/2.50      inference(unflattening,[status(thm)],[c_333]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_338,plain,
% 15.20/2.50      ( r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1) ),
% 15.20/2.50      inference(global_propositional_subsumption,
% 15.20/2.50                [status(thm)],
% 15.20/2.50                [c_334,c_27,c_25]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1071,plain,
% 15.20/2.50      ( r1_tarski(k7_relset_1(sK1,sK1,sK3,X0),sK1) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_3197,plain,
% 15.20/2.50      ( r1_tarski(k9_relat_1(sK3,X0),sK1) = iProver_top ),
% 15.20/2.50      inference(demodulation,[status(thm)],[c_3099,c_1071]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_3199,plain,
% 15.20/2.50      ( r1_tarski(k9_relat_1(sK3,sK1),sK1) = iProver_top ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_3197]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_5,plain,
% 15.20/2.50      ( ~ v1_relat_1(X0)
% 15.20/2.50      | ~ v1_relat_1(X1)
% 15.20/2.50      | k2_relat_1(k5_relat_1(X1,X0)) = k9_relat_1(X0,k2_relat_1(X1)) ),
% 15.20/2.50      inference(cnf_transformation,[],[f65]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1450,plain,
% 15.20/2.50      ( ~ v1_relat_1(X0)
% 15.20/2.50      | ~ v1_relat_1(sK3)
% 15.20/2.50      | k2_relat_1(k5_relat_1(X0,sK3)) = k9_relat_1(sK3,k2_relat_1(X0)) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_5]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1747,plain,
% 15.20/2.50      ( ~ v1_relat_1(sK2)
% 15.20/2.50      | ~ v1_relat_1(sK3)
% 15.20/2.50      | k2_relat_1(k5_relat_1(sK2,sK3)) = k9_relat_1(sK3,k2_relat_1(sK2)) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_1450]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_3,plain,
% 15.20/2.50      ( ~ v1_relat_1(X0)
% 15.20/2.50      | ~ v1_relat_1(X1)
% 15.20/2.50      | v1_relat_1(k5_relat_1(X1,X0)) ),
% 15.20/2.50      inference(cnf_transformation,[],[f63]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1448,plain,
% 15.20/2.50      ( ~ v1_relat_1(X0)
% 15.20/2.50      | v1_relat_1(k5_relat_1(X0,sK3))
% 15.20/2.50      | ~ v1_relat_1(sK3) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_3]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1647,plain,
% 15.20/2.50      ( v1_relat_1(k5_relat_1(sK2,sK3))
% 15.20/2.50      | ~ v1_relat_1(sK2)
% 15.20/2.50      | ~ v1_relat_1(sK3) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_1448]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1648,plain,
% 15.20/2.50      ( v1_relat_1(k5_relat_1(sK2,sK3)) = iProver_top
% 15.20/2.50      | v1_relat_1(sK2) != iProver_top
% 15.20/2.50      | v1_relat_1(sK3) != iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_1647]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_8,plain,
% 15.20/2.50      ( ~ v1_funct_1(X0)
% 15.20/2.50      | ~ v1_funct_1(X1)
% 15.20/2.50      | ~ v1_relat_1(X0)
% 15.20/2.50      | ~ v1_relat_1(X1)
% 15.20/2.50      | k5_relat_1(X1,X0) != X1
% 15.20/2.50      | k6_partfun1(k1_relat_1(X0)) = X0
% 15.20/2.50      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f92]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1383,plain,
% 15.20/2.50      ( ~ v1_funct_1(X0)
% 15.20/2.50      | ~ v1_funct_1(sK3)
% 15.20/2.50      | ~ v1_relat_1(X0)
% 15.20/2.50      | ~ v1_relat_1(sK3)
% 15.20/2.50      | k5_relat_1(X0,sK3) != X0
% 15.20/2.50      | k6_partfun1(k1_relat_1(sK3)) = sK3
% 15.20/2.50      | k2_relat_1(X0) != k1_relat_1(sK3) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_8]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1585,plain,
% 15.20/2.50      ( ~ v1_funct_1(sK2)
% 15.20/2.50      | ~ v1_funct_1(sK3)
% 15.20/2.50      | ~ v1_relat_1(sK2)
% 15.20/2.50      | ~ v1_relat_1(sK3)
% 15.20/2.50      | k5_relat_1(sK2,sK3) != sK2
% 15.20/2.50      | k6_partfun1(k1_relat_1(sK3)) = sK3
% 15.20/2.50      | k2_relat_1(sK2) != k1_relat_1(sK3) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_1383]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_575,plain,( X0 = X0 ),theory(equality) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1567,plain,
% 15.20/2.50      ( sK3 = sK3 ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_575]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_13,plain,
% 15.20/2.50      ( r2_relset_1(X0,X1,X2,X2)
% 15.20/2.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 15.20/2.50      inference(cnf_transformation,[],[f96]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1342,plain,
% 15.20/2.50      ( r2_relset_1(X0,X0,k6_partfun1(X0),k6_partfun1(X0))
% 15.20/2.50      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_13]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1344,plain,
% 15.20/2.50      ( r2_relset_1(sK1,sK1,k6_partfun1(sK1),k6_partfun1(sK1))
% 15.20/2.50      | ~ m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_1342]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1301,plain,
% 15.20/2.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.50      | v1_relat_1(sK2) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1302,plain,
% 15.20/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 15.20/2.50      | v1_relat_1(sK2) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_1301]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1298,plain,
% 15.20/2.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
% 15.20/2.50      | v1_relat_1(sK3) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_9]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_1299,plain,
% 15.20/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top
% 15.20/2.50      | v1_relat_1(sK3) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_1298]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_600,plain,
% 15.20/2.50      ( k6_partfun1(sK1) = k6_partfun1(sK1) | sK1 != sK1 ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_583]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_0,plain,
% 15.20/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.20/2.50      inference(cnf_transformation,[],[f62]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_99,plain,
% 15.20/2.50      ( ~ r1_tarski(sK1,sK1) | sK1 = sK1 ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_0]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_2,plain,
% 15.20/2.50      ( r1_tarski(X0,X0) ),
% 15.20/2.50      inference(cnf_transformation,[],[f95]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_94,plain,
% 15.20/2.50      ( r1_tarski(X0,X0) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_96,plain,
% 15.20/2.50      ( r1_tarski(sK1,sK1) = iProver_top ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_94]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_95,plain,
% 15.20/2.50      ( r1_tarski(sK1,sK1) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_2]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_17,plain,
% 15.20/2.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 15.20/2.50      inference(cnf_transformation,[],[f93]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_52,plain,
% 15.20/2.50      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 15.20/2.50      inference(instantiation,[status(thm)],[c_17]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_22,negated_conjecture,
% 15.20/2.50      ( ~ r2_relset_1(sK1,sK1,sK3,k6_partfun1(sK1)) ),
% 15.20/2.50      inference(cnf_transformation,[],[f91]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_36,plain,
% 15.20/2.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(c_33,plain,
% 15.20/2.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 15.20/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.20/2.50  
% 15.20/2.50  cnf(contradiction,plain,
% 15.20/2.50      ( $false ),
% 15.20/2.50      inference(minisat,
% 15.20/2.50                [status(thm)],
% 15.20/2.50                [c_64653,c_59651,c_59596,c_57980,c_57310,c_52993,c_17133,
% 15.20/2.50                 c_17131,c_9839,c_8617,c_3199,c_2287,c_2047,c_1747,
% 15.20/2.50                 c_1648,c_1585,c_1567,c_1344,c_1302,c_1301,c_1299,c_1298,
% 15.20/2.50                 c_600,c_99,c_96,c_95,c_52,c_22,c_36,c_25,c_27,c_33,c_28,
% 15.20/2.50                 c_30]) ).
% 15.20/2.50  
% 15.20/2.50  
% 15.20/2.50  % SZS output end CNFRefutation for theBenchmark.p
% 15.20/2.50  
% 15.20/2.50  ------                               Statistics
% 15.20/2.50  
% 15.20/2.50  ------ General
% 15.20/2.50  
% 15.20/2.50  abstr_ref_over_cycles:                  0
% 15.20/2.50  abstr_ref_under_cycles:                 0
% 15.20/2.50  gc_basic_clause_elim:                   0
% 15.20/2.50  forced_gc_time:                         0
% 15.20/2.50  parsing_time:                           0.01
% 15.20/2.50  unif_index_cands_time:                  0.
% 15.20/2.50  unif_index_add_time:                    0.
% 15.20/2.50  orderings_time:                         0.
% 15.20/2.50  out_proof_time:                         0.013
% 15.20/2.50  total_time:                             1.821
% 15.20/2.50  num_of_symbols:                         54
% 15.20/2.50  num_of_terms:                           70424
% 15.20/2.50  
% 15.20/2.50  ------ Preprocessing
% 15.20/2.50  
% 15.20/2.50  num_of_splits:                          0
% 15.20/2.50  num_of_split_atoms:                     0
% 15.20/2.50  num_of_reused_defs:                     0
% 15.20/2.50  num_eq_ax_congr_red:                    31
% 15.20/2.50  num_of_sem_filtered_clauses:            1
% 15.20/2.50  num_of_subtypes:                        0
% 15.20/2.50  monotx_restored_types:                  0
% 15.20/2.50  sat_num_of_epr_types:                   0
% 15.20/2.50  sat_num_of_non_cyclic_types:            0
% 15.20/2.50  sat_guarded_non_collapsed_types:        0
% 15.20/2.50  num_pure_diseq_elim:                    0
% 15.20/2.50  simp_replaced_by:                       0
% 15.20/2.50  res_preprocessed:                       159
% 15.20/2.50  prep_upred:                             0
% 15.20/2.50  prep_unflattend:                        10
% 15.20/2.50  smt_new_axioms:                         0
% 15.20/2.50  pred_elim_cands:                        5
% 15.20/2.50  pred_elim:                              1
% 15.20/2.50  pred_elim_cl:                           0
% 15.20/2.50  pred_elim_cycles:                       3
% 15.20/2.50  merged_defs:                            0
% 15.20/2.50  merged_defs_ncl:                        0
% 15.20/2.50  bin_hyper_res:                          0
% 15.20/2.50  prep_cycles:                            4
% 15.20/2.50  pred_elim_time:                         0.002
% 15.20/2.50  splitting_time:                         0.
% 15.20/2.50  sem_filter_time:                        0.
% 15.20/2.50  monotx_time:                            0.001
% 15.20/2.50  subtype_inf_time:                       0.
% 15.20/2.50  
% 15.20/2.50  ------ Problem properties
% 15.20/2.50  
% 15.20/2.50  clauses:                                30
% 15.20/2.50  conjectures:                            7
% 15.20/2.50  epr:                                    4
% 15.20/2.50  horn:                                   30
% 15.20/2.50  ground:                                 9
% 15.20/2.50  unary:                                  13
% 15.20/2.50  binary:                                 7
% 15.20/2.50  lits:                                   67
% 15.20/2.50  lits_eq:                                17
% 15.20/2.50  fd_pure:                                0
% 15.20/2.50  fd_pseudo:                              0
% 15.20/2.50  fd_cond:                                0
% 15.20/2.50  fd_pseudo_cond:                         2
% 15.20/2.50  ac_symbols:                             0
% 15.20/2.50  
% 15.20/2.50  ------ Propositional Solver
% 15.20/2.50  
% 15.20/2.50  prop_solver_calls:                      43
% 15.20/2.50  prop_fast_solver_calls:                 2307
% 15.20/2.50  smt_solver_calls:                       0
% 15.20/2.50  smt_fast_solver_calls:                  0
% 15.20/2.50  prop_num_of_clauses:                    26781
% 15.20/2.50  prop_preprocess_simplified:             46670
% 15.20/2.50  prop_fo_subsumed:                       34
% 15.20/2.50  prop_solver_time:                       0.
% 15.20/2.50  smt_solver_time:                        0.
% 15.20/2.50  smt_fast_solver_time:                   0.
% 15.20/2.50  prop_fast_solver_time:                  0.
% 15.20/2.50  prop_unsat_core_time:                   0.002
% 15.20/2.50  
% 15.20/2.50  ------ QBF
% 15.20/2.50  
% 15.20/2.50  qbf_q_res:                              0
% 15.20/2.50  qbf_num_tautologies:                    0
% 15.20/2.50  qbf_prep_cycles:                        0
% 15.20/2.50  
% 15.20/2.50  ------ BMC1
% 15.20/2.50  
% 15.20/2.50  bmc1_current_bound:                     -1
% 15.20/2.50  bmc1_last_solved_bound:                 -1
% 15.20/2.50  bmc1_unsat_core_size:                   -1
% 15.20/2.50  bmc1_unsat_core_parents_size:           -1
% 15.20/2.50  bmc1_merge_next_fun:                    0
% 15.20/2.50  bmc1_unsat_core_clauses_time:           0.
% 15.20/2.50  
% 15.20/2.50  ------ Instantiation
% 15.20/2.50  
% 15.20/2.50  inst_num_of_clauses:                    1119
% 15.20/2.50  inst_num_in_passive:                    242
% 15.20/2.50  inst_num_in_active:                     3500
% 15.20/2.50  inst_num_in_unprocessed:                287
% 15.20/2.50  inst_num_of_loops:                      3602
% 15.20/2.50  inst_num_of_learning_restarts:          1
% 15.20/2.50  inst_num_moves_active_passive:          93
% 15.20/2.50  inst_lit_activity:                      0
% 15.20/2.50  inst_lit_activity_moves:                2
% 15.20/2.50  inst_num_tautologies:                   0
% 15.20/2.50  inst_num_prop_implied:                  0
% 15.20/2.50  inst_num_existing_simplified:           0
% 15.20/2.50  inst_num_eq_res_simplified:             0
% 15.20/2.50  inst_num_child_elim:                    0
% 15.20/2.50  inst_num_of_dismatching_blockings:      3324
% 15.20/2.50  inst_num_of_non_proper_insts:           7865
% 15.20/2.50  inst_num_of_duplicates:                 0
% 15.20/2.50  inst_inst_num_from_inst_to_res:         0
% 15.20/2.50  inst_dismatching_checking_time:         0.
% 15.20/2.50  
% 15.20/2.50  ------ Resolution
% 15.20/2.50  
% 15.20/2.50  res_num_of_clauses:                     49
% 15.20/2.50  res_num_in_passive:                     49
% 15.20/2.50  res_num_in_active:                      0
% 15.20/2.50  res_num_of_loops:                       163
% 15.20/2.50  res_forward_subset_subsumed:            680
% 15.20/2.50  res_backward_subset_subsumed:           16
% 15.20/2.50  res_forward_subsumed:                   0
% 15.20/2.50  res_backward_subsumed:                  0
% 15.20/2.50  res_forward_subsumption_resolution:     0
% 15.20/2.50  res_backward_subsumption_resolution:    0
% 15.20/2.50  res_clause_to_clause_subsumption:       9956
% 15.20/2.50  res_orphan_elimination:                 0
% 15.20/2.50  res_tautology_del:                      655
% 15.20/2.50  res_num_eq_res_simplified:              0
% 15.20/2.50  res_num_sel_changes:                    0
% 15.20/2.50  res_moves_from_active_to_pass:          0
% 15.20/2.50  
% 15.20/2.50  ------ Superposition
% 15.20/2.50  
% 15.20/2.50  sup_time_total:                         0.
% 15.20/2.50  sup_time_generating:                    0.
% 15.20/2.50  sup_time_sim_full:                      0.
% 15.20/2.50  sup_time_sim_immed:                     0.
% 15.20/2.50  
% 15.20/2.50  sup_num_of_clauses:                     1839
% 15.20/2.50  sup_num_in_active:                      676
% 15.20/2.50  sup_num_in_passive:                     1163
% 15.20/2.50  sup_num_of_loops:                       720
% 15.20/2.50  sup_fw_superposition:                   1575
% 15.20/2.50  sup_bw_superposition:                   288
% 15.20/2.50  sup_immediate_simplified:               292
% 15.20/2.50  sup_given_eliminated:                   0
% 15.20/2.50  comparisons_done:                       0
% 15.20/2.50  comparisons_avoided:                    0
% 15.20/2.50  
% 15.20/2.50  ------ Simplifications
% 15.20/2.50  
% 15.20/2.50  
% 15.20/2.50  sim_fw_subset_subsumed:                 6
% 15.20/2.50  sim_bw_subset_subsumed:                 0
% 15.20/2.50  sim_fw_subsumed:                        2
% 15.20/2.50  sim_bw_subsumed:                        0
% 15.20/2.50  sim_fw_subsumption_res:                 0
% 15.20/2.50  sim_bw_subsumption_res:                 0
% 15.20/2.50  sim_tautology_del:                      4
% 15.20/2.50  sim_eq_tautology_del:                   12
% 15.20/2.50  sim_eq_res_simp:                        0
% 15.20/2.50  sim_fw_demodulated:                     32
% 15.20/2.50  sim_bw_demodulated:                     44
% 15.20/2.50  sim_light_normalised:                   261
% 15.20/2.50  sim_joinable_taut:                      0
% 15.20/2.50  sim_joinable_simp:                      0
% 15.20/2.50  sim_ac_normalised:                      0
% 15.20/2.50  sim_smt_subsumption:                    0
% 15.20/2.50  
%------------------------------------------------------------------------------
