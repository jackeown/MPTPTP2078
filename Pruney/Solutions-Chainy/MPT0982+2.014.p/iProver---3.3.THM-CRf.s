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
% DateTime   : Thu Dec  3 12:01:39 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 7.57s
% Verified   : 
% Statistics : Number of formulae       :  164 (1101 expanded)
%              Number of clauses        :   98 ( 345 expanded)
%              Number of leaves         :   17 ( 268 expanded)
%              Depth                    :   22
%              Number of atoms          :  507 (7480 expanded)
%              Number of equality atoms :  230 (2520 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

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

fof(f80,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

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

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

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

fof(f81,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f14])).

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

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f84,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1172,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1174,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1177,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1178,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2810,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1177,c_1178])).

cnf(c_5422,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_2810])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5651,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5422,c_39])).

cnf(c_5652,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5651])).

cnf(c_5659,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_5652])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1175,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2673,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1175])).

cnf(c_2878,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2673,c_39])).

cnf(c_2879,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_2878])).

cnf(c_2886,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_2879])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_3011,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2886,c_36])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3013,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3011,c_29])).

cnf(c_5663,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5659,c_3011,c_3013])).

cnf(c_5672,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5663,c_36])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1180,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1523,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1180])).

cnf(c_1522,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1180])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1182,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2529,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1522,c_1182])).

cnf(c_3817,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1523,c_2529])).

cnf(c_5674,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5672,c_3817])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1184,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_5830,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5674,c_1184])).

cnf(c_41,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1246,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1303,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1246])).

cnf(c_1304,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1303])).

cnf(c_6245,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5830,c_41,c_1304])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_391,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_13])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_391])).

cnf(c_396,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_392,c_12])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_396])).

cnf(c_1169,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_1906,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1174,c_1169])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1186,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2102,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1186])).

cnf(c_6250,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_6245,c_2102])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1181,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1569,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1522,c_1181])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1179,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2045,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1174,c_1179])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_532,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_533,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_532])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_535,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_533,c_30,c_27])).

cnf(c_2047,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2045,c_535])).

cnf(c_3376,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1569,c_1569,c_2047])).

cnf(c_20641,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_6250,c_3376])).

cnf(c_1907,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1172,c_1169])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_412,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_28])).

cnf(c_413,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_412])).

cnf(c_417,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_413,c_32])).

cnf(c_1168,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_419,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_417])).

cnf(c_1830,plain,
    ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1168,c_41,c_419,c_1304])).

cnf(c_1831,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1830])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_433,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_28])).

cnf(c_434,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_438,plain,
    ( ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_434,c_32])).

cnf(c_1167,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_438])).

cnf(c_1647,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1167,c_32,c_30,c_434,c_1303])).

cnf(c_1836,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1831,c_1647])).

cnf(c_2097,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2047,c_1836])).

cnf(c_3764,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1907,c_2097])).

cnf(c_4327,plain,
    ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_3817,c_3764])).

cnf(c_14839,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_4327,c_4327,c_5672])).

cnf(c_20915,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_20641,c_14839])).

cnf(c_1950,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1172,c_1178])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2333,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_1950,c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_20915,c_2333])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.57/1.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.57/1.51  
% 7.57/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.57/1.51  
% 7.57/1.51  ------  iProver source info
% 7.57/1.51  
% 7.57/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.57/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.57/1.51  git: non_committed_changes: false
% 7.57/1.51  git: last_make_outside_of_git: false
% 7.57/1.51  
% 7.57/1.51  ------ 
% 7.57/1.51  
% 7.57/1.51  ------ Input Options
% 7.57/1.51  
% 7.57/1.51  --out_options                           all
% 7.57/1.51  --tptp_safe_out                         true
% 7.57/1.51  --problem_path                          ""
% 7.57/1.51  --include_path                          ""
% 7.57/1.51  --clausifier                            res/vclausify_rel
% 7.57/1.51  --clausifier_options                    ""
% 7.57/1.51  --stdin                                 false
% 7.57/1.51  --stats_out                             all
% 7.57/1.51  
% 7.57/1.51  ------ General Options
% 7.57/1.51  
% 7.57/1.51  --fof                                   false
% 7.57/1.51  --time_out_real                         305.
% 7.57/1.51  --time_out_virtual                      -1.
% 7.57/1.51  --symbol_type_check                     false
% 7.57/1.51  --clausify_out                          false
% 7.57/1.51  --sig_cnt_out                           false
% 7.57/1.51  --trig_cnt_out                          false
% 7.57/1.51  --trig_cnt_out_tolerance                1.
% 7.57/1.51  --trig_cnt_out_sk_spl                   false
% 7.57/1.51  --abstr_cl_out                          false
% 7.57/1.51  
% 7.57/1.51  ------ Global Options
% 7.57/1.51  
% 7.57/1.51  --schedule                              default
% 7.57/1.51  --add_important_lit                     false
% 7.57/1.51  --prop_solver_per_cl                    1000
% 7.57/1.51  --min_unsat_core                        false
% 7.57/1.51  --soft_assumptions                      false
% 7.57/1.51  --soft_lemma_size                       3
% 7.57/1.51  --prop_impl_unit_size                   0
% 7.57/1.51  --prop_impl_unit                        []
% 7.57/1.51  --share_sel_clauses                     true
% 7.57/1.51  --reset_solvers                         false
% 7.57/1.51  --bc_imp_inh                            [conj_cone]
% 7.57/1.51  --conj_cone_tolerance                   3.
% 7.57/1.51  --extra_neg_conj                        none
% 7.57/1.51  --large_theory_mode                     true
% 7.57/1.51  --prolific_symb_bound                   200
% 7.57/1.51  --lt_threshold                          2000
% 7.57/1.51  --clause_weak_htbl                      true
% 7.57/1.51  --gc_record_bc_elim                     false
% 7.57/1.51  
% 7.57/1.51  ------ Preprocessing Options
% 7.57/1.51  
% 7.57/1.51  --preprocessing_flag                    true
% 7.57/1.51  --time_out_prep_mult                    0.1
% 7.57/1.51  --splitting_mode                        input
% 7.57/1.51  --splitting_grd                         true
% 7.57/1.51  --splitting_cvd                         false
% 7.57/1.51  --splitting_cvd_svl                     false
% 7.57/1.51  --splitting_nvd                         32
% 7.57/1.51  --sub_typing                            true
% 7.57/1.51  --prep_gs_sim                           true
% 7.57/1.51  --prep_unflatten                        true
% 7.57/1.51  --prep_res_sim                          true
% 7.57/1.51  --prep_upred                            true
% 7.57/1.51  --prep_sem_filter                       exhaustive
% 7.57/1.51  --prep_sem_filter_out                   false
% 7.57/1.51  --pred_elim                             true
% 7.57/1.51  --res_sim_input                         true
% 7.57/1.51  --eq_ax_congr_red                       true
% 7.57/1.51  --pure_diseq_elim                       true
% 7.57/1.51  --brand_transform                       false
% 7.57/1.51  --non_eq_to_eq                          false
% 7.57/1.51  --prep_def_merge                        true
% 7.57/1.51  --prep_def_merge_prop_impl              false
% 7.57/1.51  --prep_def_merge_mbd                    true
% 7.57/1.51  --prep_def_merge_tr_red                 false
% 7.57/1.51  --prep_def_merge_tr_cl                  false
% 7.57/1.51  --smt_preprocessing                     true
% 7.57/1.51  --smt_ac_axioms                         fast
% 7.57/1.51  --preprocessed_out                      false
% 7.57/1.51  --preprocessed_stats                    false
% 7.57/1.51  
% 7.57/1.51  ------ Abstraction refinement Options
% 7.57/1.51  
% 7.57/1.51  --abstr_ref                             []
% 7.57/1.51  --abstr_ref_prep                        false
% 7.57/1.51  --abstr_ref_until_sat                   false
% 7.57/1.51  --abstr_ref_sig_restrict                funpre
% 7.57/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.51  --abstr_ref_under                       []
% 7.57/1.51  
% 7.57/1.51  ------ SAT Options
% 7.57/1.51  
% 7.57/1.51  --sat_mode                              false
% 7.57/1.51  --sat_fm_restart_options                ""
% 7.57/1.51  --sat_gr_def                            false
% 7.57/1.51  --sat_epr_types                         true
% 7.57/1.51  --sat_non_cyclic_types                  false
% 7.57/1.51  --sat_finite_models                     false
% 7.57/1.51  --sat_fm_lemmas                         false
% 7.57/1.51  --sat_fm_prep                           false
% 7.57/1.51  --sat_fm_uc_incr                        true
% 7.57/1.51  --sat_out_model                         small
% 7.57/1.51  --sat_out_clauses                       false
% 7.57/1.51  
% 7.57/1.51  ------ QBF Options
% 7.57/1.51  
% 7.57/1.51  --qbf_mode                              false
% 7.57/1.51  --qbf_elim_univ                         false
% 7.57/1.51  --qbf_dom_inst                          none
% 7.57/1.51  --qbf_dom_pre_inst                      false
% 7.57/1.51  --qbf_sk_in                             false
% 7.57/1.51  --qbf_pred_elim                         true
% 7.57/1.51  --qbf_split                             512
% 7.57/1.51  
% 7.57/1.51  ------ BMC1 Options
% 7.57/1.51  
% 7.57/1.51  --bmc1_incremental                      false
% 7.57/1.51  --bmc1_axioms                           reachable_all
% 7.57/1.51  --bmc1_min_bound                        0
% 7.57/1.51  --bmc1_max_bound                        -1
% 7.57/1.51  --bmc1_max_bound_default                -1
% 7.57/1.51  --bmc1_symbol_reachability              true
% 7.57/1.51  --bmc1_property_lemmas                  false
% 7.57/1.51  --bmc1_k_induction                      false
% 7.57/1.51  --bmc1_non_equiv_states                 false
% 7.57/1.51  --bmc1_deadlock                         false
% 7.57/1.51  --bmc1_ucm                              false
% 7.57/1.51  --bmc1_add_unsat_core                   none
% 7.57/1.51  --bmc1_unsat_core_children              false
% 7.57/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.51  --bmc1_out_stat                         full
% 7.57/1.51  --bmc1_ground_init                      false
% 7.57/1.51  --bmc1_pre_inst_next_state              false
% 7.57/1.51  --bmc1_pre_inst_state                   false
% 7.57/1.51  --bmc1_pre_inst_reach_state             false
% 7.57/1.51  --bmc1_out_unsat_core                   false
% 7.57/1.51  --bmc1_aig_witness_out                  false
% 7.57/1.51  --bmc1_verbose                          false
% 7.57/1.51  --bmc1_dump_clauses_tptp                false
% 7.57/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.51  --bmc1_dump_file                        -
% 7.57/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.51  --bmc1_ucm_extend_mode                  1
% 7.57/1.51  --bmc1_ucm_init_mode                    2
% 7.57/1.51  --bmc1_ucm_cone_mode                    none
% 7.57/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.51  --bmc1_ucm_relax_model                  4
% 7.57/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.51  --bmc1_ucm_layered_model                none
% 7.57/1.51  --bmc1_ucm_max_lemma_size               10
% 7.57/1.51  
% 7.57/1.51  ------ AIG Options
% 7.57/1.51  
% 7.57/1.51  --aig_mode                              false
% 7.57/1.51  
% 7.57/1.51  ------ Instantiation Options
% 7.57/1.51  
% 7.57/1.51  --instantiation_flag                    true
% 7.57/1.51  --inst_sos_flag                         true
% 7.57/1.51  --inst_sos_phase                        true
% 7.57/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.51  --inst_lit_sel_side                     num_symb
% 7.57/1.51  --inst_solver_per_active                1400
% 7.57/1.51  --inst_solver_calls_frac                1.
% 7.57/1.51  --inst_passive_queue_type               priority_queues
% 7.57/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.51  --inst_passive_queues_freq              [25;2]
% 7.57/1.51  --inst_dismatching                      true
% 7.57/1.51  --inst_eager_unprocessed_to_passive     true
% 7.57/1.51  --inst_prop_sim_given                   true
% 7.57/1.51  --inst_prop_sim_new                     false
% 7.57/1.51  --inst_subs_new                         false
% 7.57/1.51  --inst_eq_res_simp                      false
% 7.57/1.51  --inst_subs_given                       false
% 7.57/1.51  --inst_orphan_elimination               true
% 7.57/1.51  --inst_learning_loop_flag               true
% 7.57/1.51  --inst_learning_start                   3000
% 7.57/1.51  --inst_learning_factor                  2
% 7.57/1.51  --inst_start_prop_sim_after_learn       3
% 7.57/1.51  --inst_sel_renew                        solver
% 7.57/1.51  --inst_lit_activity_flag                true
% 7.57/1.51  --inst_restr_to_given                   false
% 7.57/1.51  --inst_activity_threshold               500
% 7.57/1.51  --inst_out_proof                        true
% 7.57/1.51  
% 7.57/1.51  ------ Resolution Options
% 7.57/1.51  
% 7.57/1.51  --resolution_flag                       true
% 7.57/1.51  --res_lit_sel                           adaptive
% 7.57/1.51  --res_lit_sel_side                      none
% 7.57/1.51  --res_ordering                          kbo
% 7.57/1.51  --res_to_prop_solver                    active
% 7.57/1.51  --res_prop_simpl_new                    false
% 7.57/1.51  --res_prop_simpl_given                  true
% 7.57/1.51  --res_passive_queue_type                priority_queues
% 7.57/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.51  --res_passive_queues_freq               [15;5]
% 7.57/1.51  --res_forward_subs                      full
% 7.57/1.51  --res_backward_subs                     full
% 7.57/1.51  --res_forward_subs_resolution           true
% 7.57/1.51  --res_backward_subs_resolution          true
% 7.57/1.51  --res_orphan_elimination                true
% 7.57/1.51  --res_time_limit                        2.
% 7.57/1.51  --res_out_proof                         true
% 7.57/1.51  
% 7.57/1.51  ------ Superposition Options
% 7.57/1.51  
% 7.57/1.51  --superposition_flag                    true
% 7.57/1.51  --sup_passive_queue_type                priority_queues
% 7.57/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.51  --demod_completeness_check              fast
% 7.57/1.51  --demod_use_ground                      true
% 7.57/1.51  --sup_to_prop_solver                    passive
% 7.57/1.51  --sup_prop_simpl_new                    true
% 7.57/1.51  --sup_prop_simpl_given                  true
% 7.57/1.51  --sup_fun_splitting                     true
% 7.57/1.51  --sup_smt_interval                      50000
% 7.57/1.51  
% 7.57/1.51  ------ Superposition Simplification Setup
% 7.57/1.51  
% 7.57/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.57/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.57/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.57/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.57/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.57/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.57/1.51  --sup_immed_triv                        [TrivRules]
% 7.57/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_immed_bw_main                     []
% 7.57/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.57/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_input_bw                          []
% 7.57/1.51  
% 7.57/1.51  ------ Combination Options
% 7.57/1.51  
% 7.57/1.51  --comb_res_mult                         3
% 7.57/1.51  --comb_sup_mult                         2
% 7.57/1.51  --comb_inst_mult                        10
% 7.57/1.51  
% 7.57/1.51  ------ Debug Options
% 7.57/1.51  
% 7.57/1.51  --dbg_backtrace                         false
% 7.57/1.51  --dbg_dump_prop_clauses                 false
% 7.57/1.51  --dbg_dump_prop_clauses_file            -
% 7.57/1.51  --dbg_out_stat                          false
% 7.57/1.51  ------ Parsing...
% 7.57/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.57/1.51  
% 7.57/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.57/1.51  
% 7.57/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.57/1.51  
% 7.57/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.57/1.51  ------ Proving...
% 7.57/1.51  ------ Problem Properties 
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  clauses                                 29
% 7.57/1.51  conjectures                             7
% 7.57/1.51  EPR                                     5
% 7.57/1.51  Horn                                    26
% 7.57/1.51  unary                                   9
% 7.57/1.51  binary                                  10
% 7.57/1.51  lits                                    67
% 7.57/1.51  lits eq                                 26
% 7.57/1.51  fd_pure                                 0
% 7.57/1.51  fd_pseudo                               0
% 7.57/1.51  fd_cond                                 0
% 7.57/1.51  fd_pseudo_cond                          1
% 7.57/1.51  AC symbols                              0
% 7.57/1.51  
% 7.57/1.51  ------ Schedule dynamic 5 is on 
% 7.57/1.51  
% 7.57/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  ------ 
% 7.57/1.51  Current options:
% 7.57/1.51  ------ 
% 7.57/1.51  
% 7.57/1.51  ------ Input Options
% 7.57/1.51  
% 7.57/1.51  --out_options                           all
% 7.57/1.51  --tptp_safe_out                         true
% 7.57/1.51  --problem_path                          ""
% 7.57/1.51  --include_path                          ""
% 7.57/1.51  --clausifier                            res/vclausify_rel
% 7.57/1.51  --clausifier_options                    ""
% 7.57/1.51  --stdin                                 false
% 7.57/1.51  --stats_out                             all
% 7.57/1.51  
% 7.57/1.51  ------ General Options
% 7.57/1.51  
% 7.57/1.51  --fof                                   false
% 7.57/1.51  --time_out_real                         305.
% 7.57/1.51  --time_out_virtual                      -1.
% 7.57/1.51  --symbol_type_check                     false
% 7.57/1.51  --clausify_out                          false
% 7.57/1.51  --sig_cnt_out                           false
% 7.57/1.51  --trig_cnt_out                          false
% 7.57/1.51  --trig_cnt_out_tolerance                1.
% 7.57/1.51  --trig_cnt_out_sk_spl                   false
% 7.57/1.51  --abstr_cl_out                          false
% 7.57/1.51  
% 7.57/1.51  ------ Global Options
% 7.57/1.51  
% 7.57/1.51  --schedule                              default
% 7.57/1.51  --add_important_lit                     false
% 7.57/1.51  --prop_solver_per_cl                    1000
% 7.57/1.51  --min_unsat_core                        false
% 7.57/1.51  --soft_assumptions                      false
% 7.57/1.51  --soft_lemma_size                       3
% 7.57/1.51  --prop_impl_unit_size                   0
% 7.57/1.51  --prop_impl_unit                        []
% 7.57/1.51  --share_sel_clauses                     true
% 7.57/1.51  --reset_solvers                         false
% 7.57/1.51  --bc_imp_inh                            [conj_cone]
% 7.57/1.51  --conj_cone_tolerance                   3.
% 7.57/1.51  --extra_neg_conj                        none
% 7.57/1.51  --large_theory_mode                     true
% 7.57/1.51  --prolific_symb_bound                   200
% 7.57/1.51  --lt_threshold                          2000
% 7.57/1.51  --clause_weak_htbl                      true
% 7.57/1.51  --gc_record_bc_elim                     false
% 7.57/1.51  
% 7.57/1.51  ------ Preprocessing Options
% 7.57/1.51  
% 7.57/1.51  --preprocessing_flag                    true
% 7.57/1.51  --time_out_prep_mult                    0.1
% 7.57/1.51  --splitting_mode                        input
% 7.57/1.51  --splitting_grd                         true
% 7.57/1.51  --splitting_cvd                         false
% 7.57/1.51  --splitting_cvd_svl                     false
% 7.57/1.51  --splitting_nvd                         32
% 7.57/1.51  --sub_typing                            true
% 7.57/1.51  --prep_gs_sim                           true
% 7.57/1.51  --prep_unflatten                        true
% 7.57/1.51  --prep_res_sim                          true
% 7.57/1.51  --prep_upred                            true
% 7.57/1.51  --prep_sem_filter                       exhaustive
% 7.57/1.51  --prep_sem_filter_out                   false
% 7.57/1.51  --pred_elim                             true
% 7.57/1.51  --res_sim_input                         true
% 7.57/1.51  --eq_ax_congr_red                       true
% 7.57/1.51  --pure_diseq_elim                       true
% 7.57/1.51  --brand_transform                       false
% 7.57/1.51  --non_eq_to_eq                          false
% 7.57/1.51  --prep_def_merge                        true
% 7.57/1.51  --prep_def_merge_prop_impl              false
% 7.57/1.51  --prep_def_merge_mbd                    true
% 7.57/1.51  --prep_def_merge_tr_red                 false
% 7.57/1.51  --prep_def_merge_tr_cl                  false
% 7.57/1.51  --smt_preprocessing                     true
% 7.57/1.51  --smt_ac_axioms                         fast
% 7.57/1.51  --preprocessed_out                      false
% 7.57/1.51  --preprocessed_stats                    false
% 7.57/1.51  
% 7.57/1.51  ------ Abstraction refinement Options
% 7.57/1.51  
% 7.57/1.51  --abstr_ref                             []
% 7.57/1.51  --abstr_ref_prep                        false
% 7.57/1.51  --abstr_ref_until_sat                   false
% 7.57/1.51  --abstr_ref_sig_restrict                funpre
% 7.57/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.57/1.51  --abstr_ref_under                       []
% 7.57/1.51  
% 7.57/1.51  ------ SAT Options
% 7.57/1.51  
% 7.57/1.51  --sat_mode                              false
% 7.57/1.51  --sat_fm_restart_options                ""
% 7.57/1.51  --sat_gr_def                            false
% 7.57/1.51  --sat_epr_types                         true
% 7.57/1.51  --sat_non_cyclic_types                  false
% 7.57/1.51  --sat_finite_models                     false
% 7.57/1.51  --sat_fm_lemmas                         false
% 7.57/1.51  --sat_fm_prep                           false
% 7.57/1.51  --sat_fm_uc_incr                        true
% 7.57/1.51  --sat_out_model                         small
% 7.57/1.51  --sat_out_clauses                       false
% 7.57/1.51  
% 7.57/1.51  ------ QBF Options
% 7.57/1.51  
% 7.57/1.51  --qbf_mode                              false
% 7.57/1.51  --qbf_elim_univ                         false
% 7.57/1.51  --qbf_dom_inst                          none
% 7.57/1.51  --qbf_dom_pre_inst                      false
% 7.57/1.51  --qbf_sk_in                             false
% 7.57/1.51  --qbf_pred_elim                         true
% 7.57/1.51  --qbf_split                             512
% 7.57/1.51  
% 7.57/1.51  ------ BMC1 Options
% 7.57/1.51  
% 7.57/1.51  --bmc1_incremental                      false
% 7.57/1.51  --bmc1_axioms                           reachable_all
% 7.57/1.51  --bmc1_min_bound                        0
% 7.57/1.51  --bmc1_max_bound                        -1
% 7.57/1.51  --bmc1_max_bound_default                -1
% 7.57/1.51  --bmc1_symbol_reachability              true
% 7.57/1.51  --bmc1_property_lemmas                  false
% 7.57/1.51  --bmc1_k_induction                      false
% 7.57/1.51  --bmc1_non_equiv_states                 false
% 7.57/1.51  --bmc1_deadlock                         false
% 7.57/1.51  --bmc1_ucm                              false
% 7.57/1.51  --bmc1_add_unsat_core                   none
% 7.57/1.51  --bmc1_unsat_core_children              false
% 7.57/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.57/1.51  --bmc1_out_stat                         full
% 7.57/1.51  --bmc1_ground_init                      false
% 7.57/1.51  --bmc1_pre_inst_next_state              false
% 7.57/1.51  --bmc1_pre_inst_state                   false
% 7.57/1.51  --bmc1_pre_inst_reach_state             false
% 7.57/1.51  --bmc1_out_unsat_core                   false
% 7.57/1.51  --bmc1_aig_witness_out                  false
% 7.57/1.51  --bmc1_verbose                          false
% 7.57/1.51  --bmc1_dump_clauses_tptp                false
% 7.57/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.57/1.51  --bmc1_dump_file                        -
% 7.57/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.57/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.57/1.51  --bmc1_ucm_extend_mode                  1
% 7.57/1.51  --bmc1_ucm_init_mode                    2
% 7.57/1.51  --bmc1_ucm_cone_mode                    none
% 7.57/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.57/1.51  --bmc1_ucm_relax_model                  4
% 7.57/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.57/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.57/1.51  --bmc1_ucm_layered_model                none
% 7.57/1.51  --bmc1_ucm_max_lemma_size               10
% 7.57/1.51  
% 7.57/1.51  ------ AIG Options
% 7.57/1.51  
% 7.57/1.51  --aig_mode                              false
% 7.57/1.51  
% 7.57/1.51  ------ Instantiation Options
% 7.57/1.51  
% 7.57/1.51  --instantiation_flag                    true
% 7.57/1.51  --inst_sos_flag                         true
% 7.57/1.51  --inst_sos_phase                        true
% 7.57/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.57/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.57/1.51  --inst_lit_sel_side                     none
% 7.57/1.51  --inst_solver_per_active                1400
% 7.57/1.51  --inst_solver_calls_frac                1.
% 7.57/1.51  --inst_passive_queue_type               priority_queues
% 7.57/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.57/1.51  --inst_passive_queues_freq              [25;2]
% 7.57/1.51  --inst_dismatching                      true
% 7.57/1.51  --inst_eager_unprocessed_to_passive     true
% 7.57/1.51  --inst_prop_sim_given                   true
% 7.57/1.51  --inst_prop_sim_new                     false
% 7.57/1.51  --inst_subs_new                         false
% 7.57/1.51  --inst_eq_res_simp                      false
% 7.57/1.51  --inst_subs_given                       false
% 7.57/1.51  --inst_orphan_elimination               true
% 7.57/1.51  --inst_learning_loop_flag               true
% 7.57/1.51  --inst_learning_start                   3000
% 7.57/1.51  --inst_learning_factor                  2
% 7.57/1.51  --inst_start_prop_sim_after_learn       3
% 7.57/1.51  --inst_sel_renew                        solver
% 7.57/1.51  --inst_lit_activity_flag                true
% 7.57/1.51  --inst_restr_to_given                   false
% 7.57/1.51  --inst_activity_threshold               500
% 7.57/1.51  --inst_out_proof                        true
% 7.57/1.51  
% 7.57/1.51  ------ Resolution Options
% 7.57/1.51  
% 7.57/1.51  --resolution_flag                       false
% 7.57/1.51  --res_lit_sel                           adaptive
% 7.57/1.51  --res_lit_sel_side                      none
% 7.57/1.51  --res_ordering                          kbo
% 7.57/1.51  --res_to_prop_solver                    active
% 7.57/1.51  --res_prop_simpl_new                    false
% 7.57/1.51  --res_prop_simpl_given                  true
% 7.57/1.51  --res_passive_queue_type                priority_queues
% 7.57/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.57/1.51  --res_passive_queues_freq               [15;5]
% 7.57/1.51  --res_forward_subs                      full
% 7.57/1.51  --res_backward_subs                     full
% 7.57/1.51  --res_forward_subs_resolution           true
% 7.57/1.51  --res_backward_subs_resolution          true
% 7.57/1.51  --res_orphan_elimination                true
% 7.57/1.51  --res_time_limit                        2.
% 7.57/1.51  --res_out_proof                         true
% 7.57/1.51  
% 7.57/1.51  ------ Superposition Options
% 7.57/1.51  
% 7.57/1.51  --superposition_flag                    true
% 7.57/1.51  --sup_passive_queue_type                priority_queues
% 7.57/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.57/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.57/1.51  --demod_completeness_check              fast
% 7.57/1.51  --demod_use_ground                      true
% 7.57/1.51  --sup_to_prop_solver                    passive
% 7.57/1.51  --sup_prop_simpl_new                    true
% 7.57/1.51  --sup_prop_simpl_given                  true
% 7.57/1.51  --sup_fun_splitting                     true
% 7.57/1.51  --sup_smt_interval                      50000
% 7.57/1.51  
% 7.57/1.51  ------ Superposition Simplification Setup
% 7.57/1.51  
% 7.57/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.57/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.57/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.57/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.57/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.57/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.57/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.57/1.51  --sup_immed_triv                        [TrivRules]
% 7.57/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_immed_bw_main                     []
% 7.57/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.57/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.57/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.57/1.51  --sup_input_bw                          []
% 7.57/1.51  
% 7.57/1.51  ------ Combination Options
% 7.57/1.51  
% 7.57/1.51  --comb_res_mult                         3
% 7.57/1.51  --comb_sup_mult                         2
% 7.57/1.51  --comb_inst_mult                        10
% 7.57/1.51  
% 7.57/1.51  ------ Debug Options
% 7.57/1.51  
% 7.57/1.51  --dbg_backtrace                         false
% 7.57/1.51  --dbg_dump_prop_clauses                 false
% 7.57/1.51  --dbg_dump_prop_clauses_file            -
% 7.57/1.51  --dbg_out_stat                          false
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  ------ Proving...
% 7.57/1.51  
% 7.57/1.51  
% 7.57/1.51  % SZS status Theorem for theBenchmark.p
% 7.57/1.51  
% 7.57/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.57/1.51  
% 7.57/1.51  fof(f17,conjecture,(
% 7.57/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f18,negated_conjecture,(
% 7.57/1.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.57/1.51    inference(negated_conjecture,[],[f17])).
% 7.57/1.51  
% 7.57/1.51  fof(f40,plain,(
% 7.57/1.51    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.57/1.51    inference(ennf_transformation,[],[f18])).
% 7.57/1.51  
% 7.57/1.51  fof(f41,plain,(
% 7.57/1.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.57/1.51    inference(flattening,[],[f40])).
% 7.57/1.51  
% 7.57/1.51  fof(f47,plain,(
% 7.57/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.57/1.51    introduced(choice_axiom,[])).
% 7.57/1.51  
% 7.57/1.51  fof(f46,plain,(
% 7.57/1.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.57/1.51    introduced(choice_axiom,[])).
% 7.57/1.51  
% 7.57/1.51  fof(f48,plain,(
% 7.57/1.51    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.57/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f41,f47,f46])).
% 7.57/1.51  
% 7.57/1.51  fof(f77,plain,(
% 7.57/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f80,plain,(
% 7.57/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f15,axiom,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f36,plain,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.57/1.51    inference(ennf_transformation,[],[f15])).
% 7.57/1.51  
% 7.57/1.51  fof(f37,plain,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.57/1.51    inference(flattening,[],[f36])).
% 7.57/1.51  
% 7.57/1.51  fof(f73,plain,(
% 7.57/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f37])).
% 7.57/1.51  
% 7.57/1.51  fof(f13,axiom,(
% 7.57/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f33,plain,(
% 7.57/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(ennf_transformation,[],[f13])).
% 7.57/1.51  
% 7.57/1.51  fof(f65,plain,(
% 7.57/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.51    inference(cnf_transformation,[],[f33])).
% 7.57/1.51  
% 7.57/1.51  fof(f78,plain,(
% 7.57/1.51    v1_funct_1(sK4)),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f16,axiom,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f38,plain,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.57/1.51    inference(ennf_transformation,[],[f16])).
% 7.57/1.51  
% 7.57/1.51  fof(f39,plain,(
% 7.57/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.57/1.51    inference(flattening,[],[f38])).
% 7.57/1.51  
% 7.57/1.51  fof(f74,plain,(
% 7.57/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f39])).
% 7.57/1.51  
% 7.57/1.51  fof(f75,plain,(
% 7.57/1.51    v1_funct_1(sK3)),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f81,plain,(
% 7.57/1.51    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f10,axiom,(
% 7.57/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f30,plain,(
% 7.57/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(ennf_transformation,[],[f10])).
% 7.57/1.51  
% 7.57/1.51  fof(f61,plain,(
% 7.57/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.51    inference(cnf_transformation,[],[f30])).
% 7.57/1.51  
% 7.57/1.51  fof(f5,axiom,(
% 7.57/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f22,plain,(
% 7.57/1.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.57/1.51    inference(ennf_transformation,[],[f5])).
% 7.57/1.51  
% 7.57/1.51  fof(f56,plain,(
% 7.57/1.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f22])).
% 7.57/1.51  
% 7.57/1.51  fof(f3,axiom,(
% 7.57/1.51    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f20,plain,(
% 7.57/1.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.57/1.51    inference(ennf_transformation,[],[f3])).
% 7.57/1.51  
% 7.57/1.51  fof(f54,plain,(
% 7.57/1.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f20])).
% 7.57/1.51  
% 7.57/1.51  fof(f2,axiom,(
% 7.57/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f19,plain,(
% 7.57/1.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.57/1.51    inference(ennf_transformation,[],[f2])).
% 7.57/1.51  
% 7.57/1.51  fof(f44,plain,(
% 7.57/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.57/1.51    inference(nnf_transformation,[],[f19])).
% 7.57/1.51  
% 7.57/1.51  fof(f52,plain,(
% 7.57/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f44])).
% 7.57/1.51  
% 7.57/1.51  fof(f11,axiom,(
% 7.57/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f31,plain,(
% 7.57/1.51    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(ennf_transformation,[],[f11])).
% 7.57/1.51  
% 7.57/1.51  fof(f63,plain,(
% 7.57/1.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.51    inference(cnf_transformation,[],[f31])).
% 7.57/1.51  
% 7.57/1.51  fof(f1,axiom,(
% 7.57/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f42,plain,(
% 7.57/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.57/1.51    inference(nnf_transformation,[],[f1])).
% 7.57/1.51  
% 7.57/1.51  fof(f43,plain,(
% 7.57/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.57/1.51    inference(flattening,[],[f42])).
% 7.57/1.51  
% 7.57/1.51  fof(f51,plain,(
% 7.57/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f43])).
% 7.57/1.51  
% 7.57/1.51  fof(f6,axiom,(
% 7.57/1.51    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f23,plain,(
% 7.57/1.51    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 7.57/1.51    inference(ennf_transformation,[],[f6])).
% 7.57/1.51  
% 7.57/1.51  fof(f57,plain,(
% 7.57/1.51    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f23])).
% 7.57/1.51  
% 7.57/1.51  fof(f12,axiom,(
% 7.57/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f32,plain,(
% 7.57/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(ennf_transformation,[],[f12])).
% 7.57/1.51  
% 7.57/1.51  fof(f64,plain,(
% 7.57/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.51    inference(cnf_transformation,[],[f32])).
% 7.57/1.51  
% 7.57/1.51  fof(f14,axiom,(
% 7.57/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f34,plain,(
% 7.57/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(ennf_transformation,[],[f14])).
% 7.57/1.51  
% 7.57/1.51  fof(f35,plain,(
% 7.57/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(flattening,[],[f34])).
% 7.57/1.51  
% 7.57/1.51  fof(f45,plain,(
% 7.57/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.57/1.51    inference(nnf_transformation,[],[f35])).
% 7.57/1.51  
% 7.57/1.51  fof(f66,plain,(
% 7.57/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.57/1.51    inference(cnf_transformation,[],[f45])).
% 7.57/1.51  
% 7.57/1.51  fof(f79,plain,(
% 7.57/1.51    v1_funct_2(sK4,sK1,sK2)),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f83,plain,(
% 7.57/1.51    k1_xboole_0 != sK2),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f9,axiom,(
% 7.57/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f28,plain,(
% 7.57/1.51    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.57/1.51    inference(ennf_transformation,[],[f9])).
% 7.57/1.51  
% 7.57/1.51  fof(f29,plain,(
% 7.57/1.51    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.57/1.51    inference(flattening,[],[f28])).
% 7.57/1.51  
% 7.57/1.51  fof(f60,plain,(
% 7.57/1.51    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f29])).
% 7.57/1.51  
% 7.57/1.51  fof(f82,plain,(
% 7.57/1.51    v2_funct_1(sK4)),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  fof(f8,axiom,(
% 7.57/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 7.57/1.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.57/1.51  
% 7.57/1.51  fof(f26,plain,(
% 7.57/1.51    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.57/1.51    inference(ennf_transformation,[],[f8])).
% 7.57/1.51  
% 7.57/1.51  fof(f27,plain,(
% 7.57/1.51    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.57/1.51    inference(flattening,[],[f26])).
% 7.57/1.51  
% 7.57/1.51  fof(f59,plain,(
% 7.57/1.51    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.57/1.51    inference(cnf_transformation,[],[f27])).
% 7.57/1.51  
% 7.57/1.51  fof(f84,plain,(
% 7.57/1.51    k2_relset_1(sK0,sK1,sK3) != sK1),
% 7.57/1.51    inference(cnf_transformation,[],[f48])).
% 7.57/1.51  
% 7.57/1.51  cnf(c_33,negated_conjecture,
% 7.57/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.57/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.57/1.51  
% 7.57/1.51  cnf(c_1172,plain,
% 7.57/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.57/1.51      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.57/1.51  
% 7.57/1.51  cnf(c_30,negated_conjecture,
% 7.57/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.57/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.57/1.51  
% 7.57/1.51  cnf(c_1174,plain,
% 7.57/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.57/1.51      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.57/1.51  
% 7.57/1.51  cnf(c_23,plain,
% 7.57/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.57/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.57/1.52      | ~ v1_funct_1(X0)
% 7.57/1.52      | ~ v1_funct_1(X3) ),
% 7.57/1.52      inference(cnf_transformation,[],[f73]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1177,plain,
% 7.57/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.57/1.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.57/1.52      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.57/1.52      | v1_funct_1(X0) != iProver_top
% 7.57/1.52      | v1_funct_1(X3) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_16,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f65]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1178,plain,
% 7.57/1.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2810,plain,
% 7.57/1.52      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 7.57/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.57/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.57/1.52      | v1_funct_1(X5) != iProver_top
% 7.57/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1177,c_1178]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5422,plain,
% 7.57/1.52      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | v1_funct_1(X2) != iProver_top
% 7.57/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1174,c_2810]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_32,negated_conjecture,
% 7.57/1.52      ( v1_funct_1(sK4) ),
% 7.57/1.52      inference(cnf_transformation,[],[f78]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_39,plain,
% 7.57/1.52      ( v1_funct_1(sK4) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5651,plain,
% 7.57/1.52      ( v1_funct_1(X2) != iProver_top
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_5422,c_39]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5652,plain,
% 7.57/1.52      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.57/1.52      inference(renaming,[status(thm)],[c_5651]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5659,plain,
% 7.57/1.52      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 7.57/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1172,c_5652]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_25,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.57/1.52      | ~ v1_funct_1(X0)
% 7.57/1.52      | ~ v1_funct_1(X3)
% 7.57/1.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f74]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1175,plain,
% 7.57/1.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.57/1.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.57/1.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | v1_funct_1(X5) != iProver_top
% 7.57/1.52      | v1_funct_1(X4) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2673,plain,
% 7.57/1.52      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | v1_funct_1(X2) != iProver_top
% 7.57/1.52      | v1_funct_1(sK4) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1174,c_1175]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2878,plain,
% 7.57/1.52      ( v1_funct_1(X2) != iProver_top
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_2673,c_39]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2879,plain,
% 7.57/1.52      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.57/1.52      | v1_funct_1(X2) != iProver_top ),
% 7.57/1.52      inference(renaming,[status(thm)],[c_2878]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2886,plain,
% 7.57/1.52      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.57/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1172,c_2879]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_35,negated_conjecture,
% 7.57/1.52      ( v1_funct_1(sK3) ),
% 7.57/1.52      inference(cnf_transformation,[],[f75]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_36,plain,
% 7.57/1.52      ( v1_funct_1(sK3) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_3011,plain,
% 7.57/1.52      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_2886,c_36]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_29,negated_conjecture,
% 7.57/1.52      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 7.57/1.52      inference(cnf_transformation,[],[f81]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_3013,plain,
% 7.57/1.52      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_3011,c_29]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5663,plain,
% 7.57/1.52      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 7.57/1.52      | v1_funct_1(sK3) != iProver_top ),
% 7.57/1.52      inference(light_normalisation,[status(thm)],[c_5659,c_3011,c_3013]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5672,plain,
% 7.57/1.52      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_5663,c_36]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_12,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | v1_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f61]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1180,plain,
% 7.57/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.57/1.52      | v1_relat_1(X0) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1523,plain,
% 7.57/1.52      ( v1_relat_1(sK3) = iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1172,c_1180]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1522,plain,
% 7.57/1.52      ( v1_relat_1(sK4) = iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1174,c_1180]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_7,plain,
% 7.57/1.52      ( ~ v1_relat_1(X0)
% 7.57/1.52      | ~ v1_relat_1(X1)
% 7.57/1.52      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 7.57/1.52      inference(cnf_transformation,[],[f56]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1182,plain,
% 7.57/1.52      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 7.57/1.52      | v1_relat_1(X0) != iProver_top
% 7.57/1.52      | v1_relat_1(X1) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2529,plain,
% 7.57/1.52      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 7.57/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1522,c_1182]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_3817,plain,
% 7.57/1.52      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1523,c_2529]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5674,plain,
% 7.57/1.52      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_5672,c_3817]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5,plain,
% 7.57/1.52      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f54]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1184,plain,
% 7.57/1.52      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 7.57/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_5830,plain,
% 7.57/1.52      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 7.57/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_5674,c_1184]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_41,plain,
% 7.57/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1246,plain,
% 7.57/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.57/1.52      | v1_relat_1(sK4) ),
% 7.57/1.52      inference(instantiation,[status(thm)],[c_12]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1303,plain,
% 7.57/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.57/1.52      | v1_relat_1(sK4) ),
% 7.57/1.52      inference(instantiation,[status(thm)],[c_1246]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1304,plain,
% 7.57/1.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.57/1.52      | v1_relat_1(sK4) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_1303]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_6245,plain,
% 7.57/1.52      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_5830,c_41,c_1304]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_4,plain,
% 7.57/1.52      ( ~ v5_relat_1(X0,X1)
% 7.57/1.52      | r1_tarski(k2_relat_1(X0),X1)
% 7.57/1.52      | ~ v1_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f52]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_13,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | v5_relat_1(X0,X2) ),
% 7.57/1.52      inference(cnf_transformation,[],[f63]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_391,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | r1_tarski(k2_relat_1(X3),X4)
% 7.57/1.52      | ~ v1_relat_1(X3)
% 7.57/1.52      | X0 != X3
% 7.57/1.52      | X2 != X4 ),
% 7.57/1.52      inference(resolution_lifted,[status(thm)],[c_4,c_13]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_392,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.52      | ~ v1_relat_1(X0) ),
% 7.57/1.52      inference(unflattening,[status(thm)],[c_391]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_396,plain,
% 7.57/1.52      ( r1_tarski(k2_relat_1(X0),X2)
% 7.57/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_392,c_12]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_397,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.57/1.52      inference(renaming,[status(thm)],[c_396]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1169,plain,
% 7.57/1.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.57/1.52      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1906,plain,
% 7.57/1.52      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1174,c_1169]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_0,plain,
% 7.57/1.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.57/1.52      inference(cnf_transformation,[],[f51]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1186,plain,
% 7.57/1.52      ( X0 = X1
% 7.57/1.52      | r1_tarski(X0,X1) != iProver_top
% 7.57/1.52      | r1_tarski(X1,X0) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2102,plain,
% 7.57/1.52      ( k2_relat_1(sK4) = sK2
% 7.57/1.52      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1906,c_1186]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_6250,plain,
% 7.57/1.52      ( k2_relat_1(sK4) = sK2 ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_6245,c_2102]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_8,plain,
% 7.57/1.52      ( ~ v1_relat_1(X0)
% 7.57/1.52      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f57]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1181,plain,
% 7.57/1.52      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 7.57/1.52      | v1_relat_1(X0) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1569,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1522,c_1181]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_15,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.57/1.52      inference(cnf_transformation,[],[f64]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1179,plain,
% 7.57/1.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.57/1.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2045,plain,
% 7.57/1.52      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1174,c_1179]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_22,plain,
% 7.57/1.52      ( ~ v1_funct_2(X0,X1,X2)
% 7.57/1.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.57/1.52      | k1_xboole_0 = X2 ),
% 7.57/1.52      inference(cnf_transformation,[],[f66]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_31,negated_conjecture,
% 7.57/1.52      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.57/1.52      inference(cnf_transformation,[],[f79]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_532,plain,
% 7.57/1.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.57/1.52      | k1_relset_1(X1,X2,X0) = X1
% 7.57/1.52      | sK4 != X0
% 7.57/1.52      | sK2 != X2
% 7.57/1.52      | sK1 != X1
% 7.57/1.52      | k1_xboole_0 = X2 ),
% 7.57/1.52      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_533,plain,
% 7.57/1.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.57/1.52      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.57/1.52      | k1_xboole_0 = sK2 ),
% 7.57/1.52      inference(unflattening,[status(thm)],[c_532]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_27,negated_conjecture,
% 7.57/1.52      ( k1_xboole_0 != sK2 ),
% 7.57/1.52      inference(cnf_transformation,[],[f83]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_535,plain,
% 7.57/1.52      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_533,c_30,c_27]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2047,plain,
% 7.57/1.52      ( k1_relat_1(sK4) = sK1 ),
% 7.57/1.52      inference(light_normalisation,[status(thm)],[c_2045,c_535]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_3376,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 7.57/1.52      inference(light_normalisation,[status(thm)],[c_1569,c_1569,c_2047]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_20641,plain,
% 7.57/1.52      ( k10_relat_1(sK4,sK2) = sK1 ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_6250,c_3376]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1907,plain,
% 7.57/1.52      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1172,c_1169]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_11,plain,
% 7.57/1.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.57/1.52      | ~ v1_funct_1(X1)
% 7.57/1.52      | ~ v2_funct_1(X1)
% 7.57/1.52      | ~ v1_relat_1(X1)
% 7.57/1.52      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 7.57/1.52      inference(cnf_transformation,[],[f60]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_28,negated_conjecture,
% 7.57/1.52      ( v2_funct_1(sK4) ),
% 7.57/1.52      inference(cnf_transformation,[],[f82]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_412,plain,
% 7.57/1.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 7.57/1.52      | ~ v1_funct_1(X1)
% 7.57/1.52      | ~ v1_relat_1(X1)
% 7.57/1.52      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
% 7.57/1.52      | sK4 != X1 ),
% 7.57/1.52      inference(resolution_lifted,[status(thm)],[c_11,c_28]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_413,plain,
% 7.57/1.52      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 7.57/1.52      | ~ v1_funct_1(sK4)
% 7.57/1.52      | ~ v1_relat_1(sK4)
% 7.57/1.52      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 7.57/1.52      inference(unflattening,[status(thm)],[c_412]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_417,plain,
% 7.57/1.52      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 7.57/1.52      | ~ v1_relat_1(sK4)
% 7.57/1.52      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_413,c_32]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1168,plain,
% 7.57/1.52      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 7.57/1.52      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.57/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_419,plain,
% 7.57/1.52      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 7.57/1.52      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.57/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_417]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1830,plain,
% 7.57/1.52      ( r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 7.57/1.52      | k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0 ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_1168,c_41,c_419,c_1304]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1831,plain,
% 7.57/1.52      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 7.57/1.52      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 7.57/1.52      inference(renaming,[status(thm)],[c_1830]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_10,plain,
% 7.57/1.52      ( ~ v1_funct_1(X0)
% 7.57/1.52      | ~ v2_funct_1(X0)
% 7.57/1.52      | ~ v1_relat_1(X0)
% 7.57/1.52      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 7.57/1.52      inference(cnf_transformation,[],[f59]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_433,plain,
% 7.57/1.52      ( ~ v1_funct_1(X0)
% 7.57/1.52      | ~ v1_relat_1(X0)
% 7.57/1.52      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 7.57/1.52      | sK4 != X0 ),
% 7.57/1.52      inference(resolution_lifted,[status(thm)],[c_10,c_28]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_434,plain,
% 7.57/1.52      ( ~ v1_funct_1(sK4)
% 7.57/1.52      | ~ v1_relat_1(sK4)
% 7.57/1.52      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 7.57/1.52      inference(unflattening,[status(thm)],[c_433]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_438,plain,
% 7.57/1.52      ( ~ v1_relat_1(sK4)
% 7.57/1.52      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_434,c_32]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1167,plain,
% 7.57/1.52      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
% 7.57/1.52      | v1_relat_1(sK4) != iProver_top ),
% 7.57/1.52      inference(predicate_to_equality,[status(thm)],[c_438]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1647,plain,
% 7.57/1.52      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 7.57/1.52      inference(global_propositional_subsumption,
% 7.57/1.52                [status(thm)],
% 7.57/1.52                [c_1167,c_32,c_30,c_434,c_1303]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1836,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.57/1.52      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_1831,c_1647]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2097,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 7.57/1.52      | r1_tarski(X0,sK1) != iProver_top ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_2047,c_1836]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_3764,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1907,c_2097]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_4327,plain,
% 7.57/1.52      ( k10_relat_1(sK4,k2_relat_1(k5_relat_1(sK3,sK4))) = k2_relat_1(sK3) ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_3817,c_3764]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_14839,plain,
% 7.57/1.52      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 7.57/1.52      inference(light_normalisation,[status(thm)],[c_4327,c_4327,c_5672]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_20915,plain,
% 7.57/1.52      ( k2_relat_1(sK3) = sK1 ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_20641,c_14839]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_1950,plain,
% 7.57/1.52      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.57/1.52      inference(superposition,[status(thm)],[c_1172,c_1178]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_26,negated_conjecture,
% 7.57/1.52      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 7.57/1.52      inference(cnf_transformation,[],[f84]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(c_2333,plain,
% 7.57/1.52      ( k2_relat_1(sK3) != sK1 ),
% 7.57/1.52      inference(demodulation,[status(thm)],[c_1950,c_26]) ).
% 7.57/1.52  
% 7.57/1.52  cnf(contradiction,plain,
% 7.57/1.52      ( $false ),
% 7.57/1.52      inference(minisat,[status(thm)],[c_20915,c_2333]) ).
% 7.57/1.52  
% 7.57/1.52  
% 7.57/1.52  % SZS output end CNFRefutation for theBenchmark.p
% 7.57/1.52  
% 7.57/1.52  ------                               Statistics
% 7.57/1.52  
% 7.57/1.52  ------ General
% 7.57/1.52  
% 7.57/1.52  abstr_ref_over_cycles:                  0
% 7.57/1.52  abstr_ref_under_cycles:                 0
% 7.57/1.52  gc_basic_clause_elim:                   0
% 7.57/1.52  forced_gc_time:                         0
% 7.57/1.52  parsing_time:                           0.012
% 7.57/1.52  unif_index_cands_time:                  0.
% 7.57/1.52  unif_index_add_time:                    0.
% 7.57/1.52  orderings_time:                         0.
% 7.57/1.52  out_proof_time:                         0.013
% 7.57/1.52  total_time:                             0.718
% 7.57/1.52  num_of_symbols:                         57
% 7.57/1.52  num_of_terms:                           18147
% 7.57/1.52  
% 7.57/1.52  ------ Preprocessing
% 7.57/1.52  
% 7.57/1.52  num_of_splits:                          0
% 7.57/1.52  num_of_split_atoms:                     0
% 7.57/1.52  num_of_reused_defs:                     0
% 7.57/1.52  num_eq_ax_congr_red:                    22
% 7.57/1.52  num_of_sem_filtered_clauses:            1
% 7.57/1.52  num_of_subtypes:                        0
% 7.57/1.52  monotx_restored_types:                  0
% 7.57/1.52  sat_num_of_epr_types:                   0
% 7.57/1.52  sat_num_of_non_cyclic_types:            0
% 7.57/1.52  sat_guarded_non_collapsed_types:        0
% 7.57/1.52  num_pure_diseq_elim:                    0
% 7.57/1.52  simp_replaced_by:                       0
% 7.57/1.52  res_preprocessed:                       155
% 7.57/1.52  prep_upred:                             0
% 7.57/1.52  prep_unflattend:                        38
% 7.57/1.52  smt_new_axioms:                         0
% 7.57/1.52  pred_elim_cands:                        4
% 7.57/1.52  pred_elim:                              4
% 7.57/1.52  pred_elim_cl:                           6
% 7.57/1.52  pred_elim_cycles:                       6
% 7.57/1.52  merged_defs:                            0
% 7.57/1.52  merged_defs_ncl:                        0
% 7.57/1.52  bin_hyper_res:                          0
% 7.57/1.52  prep_cycles:                            4
% 7.57/1.52  pred_elim_time:                         0.006
% 7.57/1.52  splitting_time:                         0.
% 7.57/1.52  sem_filter_time:                        0.
% 7.57/1.52  monotx_time:                            0.001
% 7.57/1.52  subtype_inf_time:                       0.
% 7.57/1.52  
% 7.57/1.52  ------ Problem properties
% 7.57/1.52  
% 7.57/1.52  clauses:                                29
% 7.57/1.52  conjectures:                            7
% 7.57/1.52  epr:                                    5
% 7.57/1.52  horn:                                   26
% 7.57/1.52  ground:                                 13
% 7.57/1.52  unary:                                  9
% 7.57/1.52  binary:                                 10
% 7.57/1.52  lits:                                   67
% 7.57/1.52  lits_eq:                                26
% 7.57/1.52  fd_pure:                                0
% 7.57/1.52  fd_pseudo:                              0
% 7.57/1.52  fd_cond:                                0
% 7.57/1.52  fd_pseudo_cond:                         1
% 7.57/1.52  ac_symbols:                             0
% 7.57/1.52  
% 7.57/1.52  ------ Propositional Solver
% 7.57/1.52  
% 7.57/1.52  prop_solver_calls:                      33
% 7.57/1.52  prop_fast_solver_calls:                 1848
% 7.57/1.52  smt_solver_calls:                       0
% 7.57/1.52  smt_fast_solver_calls:                  0
% 7.57/1.52  prop_num_of_clauses:                    9696
% 7.57/1.52  prop_preprocess_simplified:             14709
% 7.57/1.52  prop_fo_subsumed:                       292
% 7.57/1.52  prop_solver_time:                       0.
% 7.57/1.52  smt_solver_time:                        0.
% 7.57/1.52  smt_fast_solver_time:                   0.
% 7.57/1.52  prop_fast_solver_time:                  0.
% 7.57/1.52  prop_unsat_core_time:                   0.001
% 7.57/1.52  
% 7.57/1.52  ------ QBF
% 7.57/1.52  
% 7.57/1.52  qbf_q_res:                              0
% 7.57/1.52  qbf_num_tautologies:                    0
% 7.57/1.52  qbf_prep_cycles:                        0
% 7.57/1.52  
% 7.57/1.52  ------ BMC1
% 7.57/1.52  
% 7.57/1.52  bmc1_current_bound:                     -1
% 7.57/1.52  bmc1_last_solved_bound:                 -1
% 7.57/1.52  bmc1_unsat_core_size:                   -1
% 7.57/1.52  bmc1_unsat_core_parents_size:           -1
% 7.57/1.52  bmc1_merge_next_fun:                    0
% 7.57/1.52  bmc1_unsat_core_clauses_time:           0.
% 7.57/1.52  
% 7.57/1.52  ------ Instantiation
% 7.57/1.52  
% 7.57/1.52  inst_num_of_clauses:                    2685
% 7.57/1.52  inst_num_in_passive:                    644
% 7.57/1.52  inst_num_in_active:                     1563
% 7.57/1.52  inst_num_in_unprocessed:                478
% 7.57/1.52  inst_num_of_loops:                      1670
% 7.57/1.52  inst_num_of_learning_restarts:          0
% 7.57/1.52  inst_num_moves_active_passive:          100
% 7.57/1.52  inst_lit_activity:                      0
% 7.57/1.52  inst_lit_activity_moves:                0
% 7.57/1.52  inst_num_tautologies:                   0
% 7.57/1.52  inst_num_prop_implied:                  0
% 7.57/1.52  inst_num_existing_simplified:           0
% 7.57/1.52  inst_num_eq_res_simplified:             0
% 7.57/1.52  inst_num_child_elim:                    0
% 7.57/1.52  inst_num_of_dismatching_blockings:      1070
% 7.57/1.52  inst_num_of_non_proper_insts:           4344
% 7.57/1.52  inst_num_of_duplicates:                 0
% 7.57/1.52  inst_inst_num_from_inst_to_res:         0
% 7.57/1.52  inst_dismatching_checking_time:         0.
% 7.57/1.52  
% 7.57/1.52  ------ Resolution
% 7.57/1.52  
% 7.57/1.52  res_num_of_clauses:                     0
% 7.57/1.52  res_num_in_passive:                     0
% 7.57/1.52  res_num_in_active:                      0
% 7.57/1.52  res_num_of_loops:                       159
% 7.57/1.52  res_forward_subset_subsumed:            328
% 7.57/1.52  res_backward_subset_subsumed:           0
% 7.57/1.52  res_forward_subsumed:                   0
% 7.57/1.52  res_backward_subsumed:                  0
% 7.57/1.52  res_forward_subsumption_resolution:     0
% 7.57/1.52  res_backward_subsumption_resolution:    0
% 7.57/1.52  res_clause_to_clause_subsumption:       2074
% 7.57/1.52  res_orphan_elimination:                 0
% 7.57/1.52  res_tautology_del:                      412
% 7.57/1.52  res_num_eq_res_simplified:              0
% 7.57/1.52  res_num_sel_changes:                    0
% 7.57/1.52  res_moves_from_active_to_pass:          0
% 7.57/1.52  
% 7.57/1.52  ------ Superposition
% 7.57/1.52  
% 7.57/1.52  sup_time_total:                         0.
% 7.57/1.52  sup_time_generating:                    0.
% 7.57/1.52  sup_time_sim_full:                      0.
% 7.57/1.52  sup_time_sim_immed:                     0.
% 7.57/1.52  
% 7.57/1.52  sup_num_of_clauses:                     910
% 7.57/1.52  sup_num_in_active:                      312
% 7.57/1.52  sup_num_in_passive:                     598
% 7.57/1.52  sup_num_of_loops:                       333
% 7.57/1.52  sup_fw_superposition:                   453
% 7.57/1.52  sup_bw_superposition:                   584
% 7.57/1.52  sup_immediate_simplified:               399
% 7.57/1.52  sup_given_eliminated:                   1
% 7.57/1.52  comparisons_done:                       0
% 7.57/1.52  comparisons_avoided:                    3
% 7.57/1.52  
% 7.57/1.52  ------ Simplifications
% 7.57/1.52  
% 7.57/1.52  
% 7.57/1.52  sim_fw_subset_subsumed:                 10
% 7.57/1.52  sim_bw_subset_subsumed:                 37
% 7.57/1.52  sim_fw_subsumed:                        10
% 7.57/1.52  sim_bw_subsumed:                        0
% 7.57/1.52  sim_fw_subsumption_res:                 0
% 7.57/1.52  sim_bw_subsumption_res:                 0
% 7.57/1.52  sim_tautology_del:                      0
% 7.57/1.52  sim_eq_tautology_del:                   61
% 7.57/1.52  sim_eq_res_simp:                        0
% 7.57/1.52  sim_fw_demodulated:                     23
% 7.57/1.52  sim_bw_demodulated:                     13
% 7.57/1.52  sim_light_normalised:                   418
% 7.57/1.52  sim_joinable_taut:                      0
% 7.57/1.52  sim_joinable_simp:                      0
% 7.57/1.52  sim_ac_normalised:                      0
% 7.57/1.52  sim_smt_subsumption:                    0
% 7.57/1.52  
%------------------------------------------------------------------------------
